-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentFreshCenterStrip
import AVRegularity.CycleWords.QuietDurationAlgebra
import AVRegularity.Proofs.GenSem.CoeffArr.Mean

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! A fresh finite parameter menu splits into its literal prefix and last child. -/

theorem independentFreshChain_succ {r : ℕ} (A : RealChain) (slots : Fin (r + 1) → ℤ)
    (birthLength : Fin (r + 1) → ℝ) (Y : Vec (4 * (r + 1))) :
    independentFreshChain A slots birthLength Y =
      let B := independentFreshChain A (fun j => slots j.castSucc)
        (fun j => birthLength j.castSucc) (independentFreshPrefixProjection r Y)
      { B with
        slots := B.slots ++ [slots (Fin.last r)]
        children := B.children ++ [independentFreshChild birthLength (Fin.last r) Y] } := by
  have hc : (fun j : Fin r => independentFreshChild (fun i => birthLength i.castSucc) j
      (independentFreshPrefixProjection r Y)) =
      fun j : Fin r => independentFreshChild birthLength j.castSucc Y := by
    funext j
    exact independentFreshPrefixProjection_child birthLength j Y
  dsimp only [independentFreshChain]
  rw [hc]
  rw [List.ofFn_succ_last (f := slots),
    List.ofFn_succ_last (f := fun j => independentFreshChild birthLength j Y)]
  simp only [List.append_assoc]

theorem independentFreshChain_geom_succ {r : ℕ} (D : OCData) (A : RealChain) (hA : A.WellSlotted)
    (slots : Fin (r + 1) → ℤ) (birthLength : Fin (r + 1) → ℝ) (Y : Vec (4 * (r + 1))) :
    let B := independentFreshChain A (fun j => slots j.castSucc)
      (fun j => birthLength j.castSucc) (independentFreshPrefixProjection r Y)
    (independentFreshChain A slots birthLength Y).geom D =
      D.childGeom (A.ctxLevel + r) B.slot
        (D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r)))
        (independentFreshChild birthLength (Fin.last r) Y) (B.geom D) := by
  dsimp only
  let B := independentFreshChain A (fun j => slots j.castSucc)
    (fun j => birthLength j.castSucc) (independentFreshPrefixProjection r Y)
  have hB := independentFreshChain_wellSlotted A hA (fun j => slots j.castSucc)
    (fun j => birthLength j.castSucc) (independentFreshPrefixProjection r Y)
  rw [independentFreshChain_succ]
  have hh := geom_append_child D B.baseLevel B.slots B.base B.children hB
    (slots (Fin.last r)) (independentFreshChild birthLength (Fin.last r) Y)
  have hctx : B.baseLevel + 1 + B.children.length = B.ctxLevel := by
    simp only [RealChain.ctxLevel, RealChain.lastLevel]
    omega
  rw [hctx] at hh
  change _ = D.childGeom B.ctxLevel B.slot
    (D.slotAnchor (B.ctxLevel + 1) (slots (Fin.last r))) _ (B.geom D) at hh
  rw [independentFreshChain_ctxLevel] at hh
  exact hh

/-! Inserting one normalized center and phase preserves the full independent coordinate norm. -/

def independentFreshInsertCoordinates (r : ℕ) :
    (Vec (4 * r) × (Vec 2 × Vec 2)) →L[ℝ] Vec (4 * (r + 1)) :=
  ContinuousLinearMap.pi (fun i =>
    if h : i.val < 4 * r then
      (ContinuousLinearMap.proj ⟨i.val, h⟩).comp (ContinuousLinearMap.fst ℝ _ _)
    else if h' : i.val < 4 * r + 2 then
      (ContinuousLinearMap.proj (⟨i.val - 4 * r, by omega⟩ : Fin 2)).comp
        ((ContinuousLinearMap.fst ℝ (Vec 2) (Vec 2)).comp (ContinuousLinearMap.snd ℝ _ _))
    else
      (ContinuousLinearMap.proj (⟨i.val - (4 * r + 2), by omega⟩ : Fin 2)).comp
        ((ContinuousLinearMap.snd ℝ (Vec 2) (Vec 2)).comp (ContinuousLinearMap.snd ℝ _ _)))

theorem independentFreshInsertCoordinates_norm_le (r : ℕ) :
    ‖independentFreshInsertCoordinates r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg Y)).2
  intro i
  dsimp only [independentFreshInsertCoordinates, ContinuousLinearMap.pi_apply]
  split
  · exact (norm_le_pi_norm Y.1 _).trans (norm_fst_le Y)
  · split
    · exact ((norm_le_pi_norm Y.2.1 _).trans (norm_fst_le Y.2)).trans (norm_snd_le Y)
    · exact ((norm_le_pi_norm Y.2.2 _).trans (norm_snd_le Y.2)).trans (norm_snd_le Y)

theorem independentFreshInsertCoordinates_prefix (r : ℕ) (Y : Vec (4 * r) × (Vec 2 × Vec 2)) :
    independentFreshPrefixProjection r (independentFreshInsertCoordinates r Y) = Y.1 := by
  funext k
  simp only [independentFreshPrefixProjection_apply, independentFreshInsertCoordinates,
    ContinuousLinearMap.pi_apply, Fin.val_castLE, dite_eq_left k.is_lt,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rfl

theorem independentFreshInsertCoordinates_last_center (r : ℕ)
    (Y : Vec (4 * r) × (Vec 2 × Vec 2)) :
    independentFreshChildProjection (Fin.last r) false (independentFreshInsertCoordinates r Y) = Y.2.1 := by
  funext k
  simp only [independentFreshChildProjection_apply, independentFreshChildCoordinate,
    Bool.false_eq_true, ite_false, Fin.val_last, independentFreshInsertCoordinates,
    ContinuousLinearMap.pi_apply]
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  have he : (⟨4 * r + 0 + k.val - 4 * r, by omega⟩ : Fin 2) = k := by
    apply Fin.ext
    dsimp only
    omega
  rw [he]
  rfl

theorem independentFreshInsertCoordinates_last_phase (r : ℕ)
    (Y : Vec (4 * r) × (Vec 2 × Vec 2)) :
    independentFreshChildProjection (Fin.last r) true (independentFreshInsertCoordinates r Y) = Y.2.2 := by
  funext k
  simp only [independentFreshChildProjection_apply, independentFreshChildCoordinate,
    ite_true, Fin.val_last, independentFreshInsertCoordinates, ContinuousLinearMap.pi_apply]
  rw [dite_eq_right (by omega), dite_eq_right (by omega)]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  have he : (⟨4 * r + 2 + k.val - (4 * r + 2), by omega⟩ : Fin 2) = k := by
    apply Fin.ext
    dsimp only
    omega
  rw [he]
  rfl

/-! One stored/native coordinate slice feeds the last-child mixed chart estimate at norm at most one. -/

def independentFreshStepCoordinates (r : ℕ) :
    (Vec (4 * (r + 1)) × Vec 2) →L[ℝ] (Vec (4 * r) × (Vec 2 × (Vec 2 × Vec 2))) :=
  ((independentFreshPrefixProjection r).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (((independentFreshChildProjection (Fin.last r) false).comp (ContinuousLinearMap.fst ℝ _ _)).prod
      (((independentFreshChildProjection (Fin.last r) true).comp (ContinuousLinearMap.fst ℝ _ _)).prod
        (ContinuousLinearMap.snd ℝ _ _)))

theorem independentFreshStepCoordinates_apply (r : ℕ) (Y : Vec (4 * (r + 1)) × Vec 2) :
    independentFreshStepCoordinates r Y =
      (independentFreshPrefixProjection r Y.1, independentFreshChildProjection (Fin.last r) false Y.1,
        independentFreshChildProjection (Fin.last r) true Y.1, Y.2) := rfl

theorem independentFreshStepCoordinates_norm_le (r : ℕ) :
    ‖independentFreshStepCoordinates r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul, independentFreshStepCoordinates_apply]
  have hb (L : Vec (4 * (r + 1)) →L[ℝ] Vec 2) (hL : ‖L‖ ≤ 1) : ‖L Y.1‖ ≤ ‖Y‖ :=
    ((L.le_opNorm Y.1).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq
      (one_mul _))).trans (norm_fst_le Y)
  have hprefix : ‖independentFreshPrefixProjection r Y.1‖ ≤ ‖Y‖ :=
    (((independentFreshPrefixProjection r).le_opNorm Y.1).trans
      ((mul_le_mul_of_nonneg_right (independentFreshPrefixProjection_norm_le r)
        (norm_nonneg _)).trans_eq (one_mul _))).trans (norm_fst_le Y)
  simp only [Prod.norm_def]
  exact max_le hprefix (max_le
    (hb _ (independentFreshChildProjection_norm_le _ _))
    (max_le (hb _ (independentFreshChildProjection_norm_le _ _)) (norm_snd_le Y)))

/-! Physical chart sampling retains each produced source weight to the first power. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

theorem JointSourceReserve.physical_chart_sample_contDiff
    {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E} (Q : JointSourceReserve H f)
    (e ell : ℝ) (G : Vec 2 → Vec 2) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (t : ℝ) :
    ContDiff ℝ (H : ℕ∞) (fun x => f t (e⁻¹ • G x) (ell • (e⁻¹ • G x))) :=
  (Q.diagonal_contDiff ell t).comp ((hG.of_le (by simp)).const_smul _)

theorem JointSourceReserve.physical_chart_sample_jet_le
    {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E} (Q : JointSourceReserve H f)
    (e ell : ℝ) (he : 0 < e) (hell : |ell| ≤ 1)
    (G : Vec 2 → Vec 2) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (K n : ℕ) (hKH : K ≤ H) (hn : n ≤ K) (θ B C : ℝ)
    (hθ : 0 ≤ θ) (hB : 0 ≤ B) (hC : 1 ≤ C)
    (hQ : ∀ k ≤ K, Q.budget k ≤ θ * B)
    (hGj : ∀ k, 1 ≤ k → k ≤ K → ∀ y, ‖iteratedFDeriv ℝ k (rescaledChart e G) y‖ ≤ C)
    (t : ℝ) (x : Vec 2) :
    e ^ n * ‖iteratedFDeriv ℝ n (fun y => f t (e⁻¹ • G y) (ell • (e⁻¹ • G y))) x‖ ≤
      θ * (K.factorial * B * C ^ K) := by
  let physical := fun y => f t (e⁻¹ • G y) (ell • (e⁻¹ • G y))
  have hphys : ContDiff ℝ (K : ℕ∞) physical :=
    (Q.physical_chart_sample_contDiff e ell G hG t).of_le (by exact_mod_cast hKH)
  have hs := CycleWords.normalizedJet_rescaling_eq n (hphys.of_le (by exact_mod_cast hn)) 1 e (e⁻¹ • x)
  simp only [one_pow, one_mul, abs_of_pos he, smul_inv_smul₀ he.ne'] at hs
  rw [← hs]
  have hf : (fun Y => physical (e • Y)) =
      (fun Y => f t Y (ell • Y)) ∘ rescaledChart e G := rfl
  rw [hf]
  refine finite_weighted_jet_composition_bound (fun Y => f t Y (ell • Y)) (rescaledChart e G)
    K n hn ((Q.diagonal_contDiff ell t).of_le (by exact_mod_cast hKH))
    ((rescaledChart_smooth e G hG).of_le (by simp)) (e⁻¹ • x) θ B C hθ hB hC ?_ ?_
  · intro k hk
    exact (Q.diagonal_jet_le ell hell k (hk.trans hKH) t _).trans (hQ k hk)
  · intro k hk hkK
    exact hGj k hk hkK _
end

/-! Appending one continuously moving center preserves indexed-center continuity. -/

theorem list_append_child_getD_center_continuous
    {E : Type*} [TopologicalSpace E] (children : E → List ChainChild)
    (last : E → ChainChild) (n : ℕ) (hlen : ∀ Y, (children Y).length = n)
    (hc : ∀ j, Continuous (fun Y => ((children Y).getD j ⟨0, 0⟩).center))
    (hlast : Continuous (fun Y => (last Y).center)) (j : ℕ) :
    Continuous (fun Y => ((children Y ++ [last Y]).getD j ⟨0, 0⟩).center) := by
  by_cases hj : j < n
  · have he : (fun Y => ((children Y ++ [last Y]).getD j ⟨0, 0⟩).center) =
        fun Y => ((children Y).getD j ⟨0, 0⟩).center := by
      funext Y
      rw [List.getD_append _ _ _ _ (by rw [hlen Y]; exact hj)]
    rw [he]
    exact hc j
  · have he : (fun Y => ((children Y ++ [last Y]).getD j ⟨0, 0⟩).center) =
        fun Y => ([last Y].getD (j - n) ⟨0, 0⟩).center := by
      funext Y
      rw [List.getD_append_right _ _ _ _ (by rw [hlen Y]; exact Nat.le_of_not_gt hj), hlen Y]
    rw [he]
    cases hh : j - n with
    | zero => simpa only [List.getD, hh, List.getElem?_cons_zero, Option.getD_some] using hlast
    | succ k =>
      simp only [List.getD, List.getElem?_cons_succ, List.getElem?_nil, Option.getD_none]
      exact continuous_const

/-! Joint reserves at the incoming slow scale control the literal physical source sample. -/

section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]


omit [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] in
theorem dimensionalSourcePhysicalChartSample_eq
    (f : ℝ → Vec 2 → Vec 2 → V) (E e : ℝ) (hE : 0 < E) (he : 0 < e)
    (G : Vec 2 → Vec 2) (t : ℝ) :
    (fun y => f t (G y) (e⁻¹ • G y)) =
    (fun y => f t (E • ((e / E) • (e⁻¹ • G y))) (e⁻¹ • G y)) := by
  funext y
  have hs : E * (e / E) * e⁻¹ = 1 := by field_simp
  rw [smul_smul, smul_smul, hs, one_smul]

theorem dimensionalSourcePhysicalChartSample_contDiff
    {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → V} {E e : ℝ}
    (Q : JointSourceReserve H (fun t z X => f t (E • X) z))
    (hE : 0 < E) (he : 0 < e) (G : Vec 2 → Vec 2)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (t : ℝ) :
    ContDiff ℝ (H : ℕ∞) (fun y => f t (G y) (e⁻¹ • G y)) := by
  rw [dimensionalSourcePhysicalChartSample_eq f E e hE he G t]
  exact Q.physical_chart_sample_contDiff e (e / E) G hG t

theorem dimensionalSourcePhysicalChartSample_jet_le
    {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → V} {E e : ℝ}
    (Q : JointSourceReserve H (fun t z X => f t (E • X) z))
    (hE : 0 < E) (he : 0 < e) (hratio : |e / E| ≤ 1)
    (G : Vec 2 → Vec 2) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (K n : ℕ) (hKH : K ≤ H) (hn : n ≤ K) (θ B C : ℝ)
    (hθ : 0 ≤ θ) (hB : 0 ≤ B) (hC : 1 ≤ C)
    (hQ : ∀ k ≤ K, Q.budget k ≤ θ * B)
    (hGj : ∀ k, 1 ≤ k → k ≤ K → ∀ y, ‖iteratedFDeriv ℝ k (rescaledChart e G) y‖ ≤ C)
    (t : ℝ) (x : Vec 2) :
    e ^ n * ‖iteratedFDeriv ℝ n (fun y => f t (G y) (e⁻¹ • G y)) x‖ ≤
      θ * (K.factorial * B * C ^ K) := by
  rw [dimensionalSourcePhysicalChartSample_eq f E e hE he G t]
  exact Q.physical_chart_sample_jet_le e (e / E) he hratio G hG K n hKH hn θ B C
    hθ hB hC hQ hGj t x
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs

/-! Independent-parameter primitive reserves produce genuine fast higher source carriers. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

theorem IndependentParameterSourceReserve.fast_contDiff {H : ℕ}
    {f : ℝ → Vec 2 → P → E} (Q : IndependentParameterSourceReserve H f)
    (t : ℝ) (Y : P) : ContDiff ℝ (H : ℕ∞) (fun z => f t z Y) :=
  (Q.regular t).comp₂ contDiff_id contDiff_const

theorem IndependentParameterSourceReserve.fast_derivative_bound {H : ℕ}
    {f : ℝ → Vec 2 → P → E} (Q : IndependentParameterSourceReserve H f)
    (n : ℕ) (hn : n ≤ H) (t : ℝ) (Y : P) (z : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun x => f t x Y) z‖ ≤ Q.budget n := by
  have hh := finite_affine_derivative_norm_le
    (fun Z : Vec 2 × P => f t Z.1 Z.2) n
    ((Q.regular t).of_le (by exact_mod_cast hn))
    (ContinuousLinearMap.inl ℝ (Vec 2) P)
    (ContinuousLinearMap.norm_inl_le_one ℝ (Vec 2) P) (0, Y) z
  have hb := hh.trans (Q.derivative_bound n hn t ((z, 0) + (0, Y)))
  simpa only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk, zero_add, add_zero] using hb

def IndependentParameterSourceReserve.higherSourceData {K : ℕ}
    {f : ℝ → Vec 2 → P → ℂ} {F : ℝ → Vec 2 → P → ComplexCellVector}
    (Qf : IndependentParameterSourceReserve K f)
    (QF : IndependentParameterSourceReserve K F) (a b : ℝ) (Y : P) :
    HigherSourceCarrierData (Set.Icc a b) K
      (fun t => cellQ0 (fun z => f t z Y)) (fun t z => F t z Y) :=
  finiteMeanFreeHigherSourceData a b K (fun t z => f t z Y) (fun t z => F t z Y)
    (fun t => Qf.fast_contDiff t Y) (fun t => QF.fast_contDiff t Y)
    (fun t => Qf.periodic t Y) (fun t => QF.periodic t Y)
    (Qf.measurable Y) (QF.measurable Y) Qf.budget QF.budget Qf.budget_nonneg QF.budget_nonneg
    (fun n hn t z => Qf.fast_derivative_bound n hn t Y z)
    (fun n hn t z => QF.fast_derivative_bound n hn t Y z)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Carrier coordinates retain every center and slow label while leaving phases unrestricted. -/

def independentFreshCarrierCoordinates (r : ℕ) :
    Vec (2 + 4 * r) →L[ℝ] ((Fin r → Vec 2) × Vec 2) :=
  ((ContinuousLinearMap.pi (fun j : Fin r => independentFreshChildProjection j false)).comp
    (independentStoredParameterProjection (4 * r))).prod (independentIntrinsicSlowProjection (4 * r))

theorem independentFreshCarrierCoordinates_apply (r : ℕ) (Y : Vec (2 + 4 * r)) :
    independentFreshCarrierCoordinates r Y =
      (fun j => independentFreshChildProjection j false (independentStoredParameterProjection (4 * r) Y),
        independentIntrinsicSlowProjection (4 * r) Y) := rfl

theorem independentFreshCarrierCoordinates_norm_le (r : ℕ) :
    ‖independentFreshCarrierCoordinates r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul, independentFreshCarrierCoordinates_apply, Prod.norm_def]
  have hp : ‖independentFreshParameterCoordinates r Y‖ ≤ ‖Y‖ :=
    ((independentFreshParameterCoordinates r).le_opNorm Y).trans
      ((mul_le_mul_of_nonneg_right (independentFreshParameterCoordinates_norm_le r) (norm_nonneg Y)).trans_eq (one_mul _))
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg Y)).2
    intro j
    have hj := (independentFreshChildProjection j false).le_opNorm
      (independentStoredParameterProjection (4 * r) Y)
    exact (hj.trans ((mul_le_mul_of_nonneg_right (independentFreshChildProjection_norm_le j false)
      (norm_nonneg _)).trans_eq (one_mul _))).trans ((norm_fst_le (independentFreshParameterCoordinates r Y)).trans hp)
  · exact (norm_snd_le (independentFreshParameterCoordinates r Y)).trans hp

theorem independentFreshCarrierCoordinates_center_bound (r : ℕ) (Y : Vec (2 + 4 * r)) (j : Fin r) :
    ‖independentFreshChildProjection j false (independentStoredParameterProjection (4 * r) Y)‖ ≤
      ‖independentFreshCarrierCoordinates r Y‖ :=
  (norm_le_pi_norm (independentFreshCarrierCoordinates r Y).1 j).trans (norm_fst_le _)

theorem independentFreshCarrierCoordinates_slow_bound (r : ℕ) (Y : Vec (2 + 4 * r)) :
    ‖independentIntrinsicSlowProjection (4 * r) Y‖ ≤ ‖independentFreshCarrierCoordinates r Y‖ := norm_snd_le (independentFreshCarrierCoordinates r Y)

theorem independentFreshCarrierCoordinates_norm_le_of_bounds (r : ℕ) (Y : Vec (2 + 4 * r))
    (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ j, ‖independentFreshChildProjection j false (independentStoredParameterProjection (4 * r) Y)‖ ≤ B)
    (hs : ‖independentIntrinsicSlowProjection (4 * r) Y‖ ≤ B) :
    ‖independentFreshCarrierCoordinates r Y‖ ≤ B := by
  rw [independentFreshCarrierCoordinates_apply, Prod.norm_def]
  exact max_le ((pi_norm_le_iff_of_nonneg hB).2 hc) hs

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Independent left application composes the literal stored matrix grades. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftApplySourceReserve_matrix_budget (H n : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (f : ℝ → P → ι → ℝ)
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (a b : ℕ) (v w : ι)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
      IndependentParameterSourceReserve H (fun t z Y => c m.val α t z Y v u))
    (Qf : ∀ u : ι, IndependentParameterSourceReserve (H + n) (fun t _ Y => f t Y u))
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hQc : ∀ m α u r, r ≤ H → (Qc m α u).budget r ≤ finiteMatrixPower M a v u * B)
    (hQf : ∀ u r, r ≤ H + n → (Qf u).budget r ≤ finiteMatrixPower M b u w * C)
    (r : ℕ) (hr : r ≤ H) :
    (independentLiftApplySourceReserve H n c L hL A f v Qc Qf).budget r ≤
      (liftApplyFiniteWordCount n : ℝ) *
        (‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * 2 ^ r * B * ((1 + ‖A‖) ^ n * C)) *
        finiteMatrixPower M (a + b) v w := by
  unfold independentLiftApplySourceReserve
  simp only [IndependentParameterSourceReserve.fintypeSum_budget]
  have hinner (m : Fin (n + 1)) (α : DerivativeWord2 m.val) :
      (∑ u, ((Qc m α u).scalarProduct
        ((Qf u).covariantWord m.val H (by omega) L hL A α)).budget r) ≤
        (‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * 2 ^ r * B * ((1 + ‖A‖) ^ n * C)) *
          finiteMatrixPower M (a + b) v w := by
    have hcov (u : ι) (j : ℕ) (hj : j ≤ H) :
        ((Qf u).covariantWord m.val H (by omega) L hL A α).budget j ≤
          finiteMatrixPower M b u w * ((1 + ‖A‖) ^ n * C) := by
      have hb := (Qf u).covariantWord_budget_le (finiteMatrixPower M b u w) C (hQf u)
        m.val H (by omega) L hL A α j hj
      apply hb.trans
      have hp : (1 + ‖A‖) ^ m.val ≤ (1 + ‖A‖) ^ n :=
        pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg A)) (by omega)
      exact (mul_le_mul_of_nonneg_right hp
        (mul_nonneg (finiteMatrixPower_nonneg M hM b u w) hC)).trans_eq (by ring)
    have hs := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) =>
      (Qc m α u).bilinear_budget_le
        ((Qf u).covariantWord m.val H (by omega) L hL A α)
        (ContinuousLinearMap.lsmul ℝ ℝ) (finiteMatrixPower M a v u)
        (finiteMatrixPower M b u w) B ((1 + ‖A‖) ^ n * C)
        (finiteMatrixPower_nonneg M hM a v u) hB (hQc m α u) (hcov u) r hr)
    apply hs.trans_eq
    rw [← Finset.sum_mul]
    have he := congrFun (congrFun (finiteMatrixPower_add M a b) v) w
    change (∑ u, finiteMatrixPower M a v u * finiteMatrixPower M b u w) = _ at he
    rw [he, mul_comm]
  have hs := Finset.sum_le_sum (fun m (_ : m ∈ Finset.univ) =>
    Finset.sum_le_sum (fun α (_ : α ∈ Finset.univ) => hinner m α))
  apply hs.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold liftApplyFiniteWordCount
  rw [Nat.cast_sum]
  rw [← Finset.sum_mul]
  ring

end AVRegularity.EntryWeakProofs
end

section
open Homogenization Set Filter Topology Metric
namespace AVRegularity.EntryWeakProofs

/-! A fixed carrier cutoff has full mixed jet prices before D and imposes no phase restriction. -/

theorem independent_fresh_carrier_cutoff_invariant_exists (r : ℕ) :
    ∃ (χ : Vec (2 + 4 * r) → ℝ) (B : ℕ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ Y, χ Y ∈ Icc 0 1) ∧ (∀ n, 0 ≤ B n) ∧
      (∀ n Y, ‖iteratedFDeriv ℝ n χ Y‖ ≤ B n) ∧
      (∀ Y ∈ tsupport χ, independentFreshCenterStrip (independentStoredParameterProjection (4 * r) Y) ∧
        ‖independentIntrinsicSlowProjection (4 * r) Y‖ ≤ 1) ∧
      (∀ Y, ‖independentFreshCarrierCoordinates r Y‖ < 1 / 4 → χ =ᶠ[𝓝 Y] fun _ => 1) ∧
      (∀ Y Z, independentFreshCarrierCoordinates r Y = independentFreshCarrierCoordinates r Z → χ Y = χ Z) := by
  let W := (Fin r → Vec 2) × Vec 2
  let c : ContDiffBump (0 : W) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let L := independentFreshCarrierCoordinates r
  let χ := (c : W → ℝ) ∘ L
  have hcSmooth : ContDiff ℝ (⊤ : ℕ∞) (c : W → ℝ) := c.contDiff
  have hb (n : ℕ) : ∃ B : ℝ, ∀ Y, ‖iteratedFDeriv ℝ n (c : W → ℝ) Y‖ ≤ B :=
    (c.hasCompactSupport.iteratedFDeriv n).exists_bound_of_continuous
      (ContDiff.continuous_iteratedFDeriv (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)) c.contDiff)
  choose B hB using hb
  have hBn n : 0 ≤ B n := (norm_nonneg (iteratedFDeriv ℝ n (c : W → ℝ) 0)).trans (hB n 0)
  refine ⟨χ, B, c.contDiff.comp L.contDiff, (fun Y => ⟨c.nonneg, c.le_one⟩), hBn, ?_, ?_, ?_, ?_⟩
  · intro n Y
    have hh := finite_affine_derivative_norm_le (c : W → ℝ) n (hcSmooth.of_le (by simp)) L
      (independentFreshCarrierCoordinates_norm_le r) 0 Y
    simp only [add_zero] at hh
    exact hh.trans (hB n (L Y))
  · intro Y hY
    have hc : L Y ∈ tsupport (c : W → ℝ) := tsupport_comp_subset_preimage c L.continuous hY
    rw [c.tsupport_eq] at hc
    have hn₀ : ‖L Y‖ ≤ (1 / 2 : ℝ) := by
      simpa only [sub_zero] using mem_closedBall_iff_norm.mp hc
    have hn : ‖L Y‖ ≤ 1 := hn₀.trans (by norm_num)
    constructor
    · intro j
      exact (independentFreshCarrierCoordinates_center_bound r Y j).trans hn
    · exact (independentFreshCarrierCoordinates_slow_bound r Y).trans hn
  · intro Y hY
    have hm : L Y ∈ ball (0 : W) c.rIn := by
      apply mem_ball_iff_norm.mpr
      simpa only [L, c, sub_zero] using hY
    exact (c.eventuallyEq_one_of_mem_ball hm).comp_tendsto L.continuous.continuousAt

  · intro Y Z hYZ
    exact congrArg (c : W → ℝ) hYZ

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Genuine independent source words commute with cell averaging and retain their primitive prices. -/

variable {d H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

local instance independentCoordinateMeanFamilyProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using AVRegularity.CycleEvolution.cellCube_volume_one⟩

def independentCoordinateMeanWord (f : ℝ → Vec 2 → Vec d → E)
    (t : ℝ) (w : List (Fin d)) (Y : Vec d) : E :=
  fieldCellMean (fun z => coordinateSourceWord f w Y t z)

theorem independent_coordinate_mean_word_bound {f : ℝ → Vec 2 → Vec d → E}
    (Q : IndependentParameterSourceReserve H f) (t : ℝ)
    (w : List (Fin d)) (hw : w.length ≤ H) (Y : Vec d) :
    ‖independentCoordinateMeanWord f t w Y‖ ≤ Q.budget w.length := by
  let R := Q.wordJet w.length 0 (by omega) (coordinateWordDirections w)
    (coordinateWordDirections_norm w)
  have hb z : ‖coordinateSourceWord f w Y t z‖ ≤ Q.budget w.length := by
    have hR : R.budget 0 = Q.budget w.length := rfl
    have hb := R.derivative_bound 0 le_rfl t (z, Y)
    rw [hR] at hb
    simpa only [coordinateSourceWord, norm_iteratedFDeriv_zero] using hb
  have hh := norm_integral_le_of_norm_le_const (ae_of_all (volume.restrict AVenhance.unitCube) hb)
  simpa only [independentCoordinateMeanWord, fieldCellMean, Measure.real, measure_univ, ENNReal.toReal_one,
    mul_one] using hh

theorem independent_coordinate_mean_word_continuous {f : ℝ → Vec 2 → Vec d → E}
    (Q : IndependentParameterSourceReserve H f) (t : ℝ)
    (w : List (Fin d)) (hw : w.length ≤ H) :
    Continuous (independentCoordinateMeanWord f t w) := by
  let R := Q.wordJet w.length 0 (by omega) (coordinateWordDirections w)
    (coordinateWordDirections_norm w)
  have hm Y : Measurable (fun z => coordinateSourceWord f w Y t z) :=
    ((R.regular t).comp₂ contDiff_id (contDiff_const (c := Y))).continuous.measurable
  have hc z : Continuous (fun Y => coordinateSourceWord f w Y t z) :=
    ((R.regular t).comp₂ (contDiff_const (c := z)) contDiff_id).continuous
  have hb z Y : ‖coordinateSourceWord f w Y t z‖ ≤ Q.budget w.length := by
    have hR : R.budget 0 = Q.budget w.length := rfl
    have hb := R.derivative_bound 0 le_rfl t (z, Y)
    rw [hR] at hb
    simpa only [coordinateSourceWord, norm_iteratedFDeriv_zero] using hb
  exact independent_parameter_integral_continuous (volume.restrict AVenhance.unitCube)
    (fun z Y => coordinateSourceWord f w Y t z) hm hc (Q.budget w.length) hb

theorem independent_coordinate_mean_word_derivative {f : ℝ → Vec 2 → Vec d → E}
    (Q : IndependentParameterSourceReserve H f) (t : ℝ)
    (w : List (Fin d)) (hw : w.length + 1 ≤ H) (i : Fin d) (Y : Vec d) :
    HasDerivAt (fun h : ℝ => independentCoordinateMeanWord f t w (Y + h • basisVec i))
      (independentCoordinateMeanWord f t (i :: w) Y) 0 := by
  let R := Q.wordJet w.length 1 hw (coordinateWordDirections w)
    (coordinateWordDirections_norm w)
  let g := fun z X => coordinateSourceWord f w X t z
  have hm X : Measurable (fun z => g z X) :=
    ((R.regular t).comp₂ contDiff_id contDiff_const).continuous.measurable
  have hd z : Differentiable ℝ (g z) :=
    ((R.regular t).comp₂ contDiff_const contDiff_id).differentiable one_ne_zero
  have hb₀ z X : ‖g z X‖ ≤ Q.budget w.length := by
    have hR : R.budget 0 = Q.budget w.length := rfl
    have hb := R.derivative_bound 0 (by omega) t (z, X)
    rw [hR] at hb
    simpa only [g, coordinateSourceWord, norm_iteratedFDeriv_zero] using hb
  have hb₁ z X : ‖fderiv ℝ (g z) X‖ ≤ Q.budget (w.length + 1) := by
    have hR : R.budget 1 = Q.budget (w.length + 1) := rfl
    have hb := R.parameter_derivative_bound 1 le_rfl t z X
    rw [hR] at hb
    simpa only [g, coordinateSourceWord, norm_iteratedFDeriv_one] using hb
  have hD := independent_parameter_integral_hasFDerivAt (volume.restrict AVenhance.unitCube)
    g hm hd _ _ hb₀ hb₁ Y
  have hline : HasDerivAt (fun h : ℝ => Y + h • basisVec i) (basisVec i) 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (basisVec i)).const_add Y
  have hh := hD.comp_hasDerivAt_of_eq 0 hline (by simp only [zero_smul, add_zero])
  have hi : Integrable (fun z => fderiv ℝ (g z) Y) (volume.restrict AVenhance.unitCube) :=
    (integrable_const (Q.budget (w.length + 1))).mono'
      (independent_fderiv_parameter_stronglyMeasurable g hm hd Y).aestronglyMeasurable
      (ae_of_all _ (fun z => hb₁ z Y))
  have he : (∫ z in AVenhance.unitCube, fderiv ℝ (g z) Y) (basisVec i) =
      independentCoordinateMeanWord f t (i :: w) Y := by
    rw [ContinuousLinearMap.integral_apply hi]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => (coordinate_source_word_cons Q i w hw Y t z).symm)
  rw [he] at hh
  exact hh

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Genuine centered coefficients make every independent left application to a coarse field centered. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independent_covariant_word_fast_independent (L : Vec 2 →L[ℝ] P)
    (A : Vec 2 →L[ℝ] ℝ) (f : ℝ → P → ℝ) (n : ℕ) (α : DerivativeWord2 n)
    (t : ℝ) (z z' : Vec 2) (Y : P) :
    independentSourceCovariantWord L A (fun t _ Y => f t Y) n α t z Y =
      independentSourceCovariantWord L A (fun t _ Y => f t Y) n α t z' Y := by
  induction n generalizing Y with
  | zero => rfl
  | succ n ih =>
    let β : DerivativeWord2 n := fun i => α i.castSucc
    have he : independentSourceCovariantWord L A (fun t _ Y => f t Y) n β t z =
        independentSourceCovariantWord L A (fun t _ Y => f t Y) n β t z' := by
      funext Y
      exact ih β Y
    change fderiv ℝ (independentSourceCovariantWord L A (fun t _ Y => f t Y) n β t z) Y
      (L (basisVec (α (Fin.last n)))) + A (basisVec (α (Fin.last n))) •
        independentSourceCovariantWord L A (fun t _ Y => f t Y) n β t z Y = _
    rw [he]
    rfl

omit [DecidableEq ι] in
theorem independent_lift_apply_mean_zero {H : ℕ} (n : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ) (f : ℝ → P → ι → ℝ) (v : ι)
    (Qc : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
      IndependentParameterSourceReserve H (fun t z Y => c m.val α t z Y v u))
    (hmean : ∀ m : Fin (n + 1), ∀ α : DerivativeWord2 m.val, ∀ u t Y,
      fieldCellMean (fun z => c m.val α t z Y v u) = 0) (t : ℝ) (Y : P) :
    fieldCellMean (fun z => independentLiftApplySource n c L A f v t z Y) = 0 := by
  let W := fun (m : Fin (n + 1)) (α : DerivativeWord2 m.val) (u : ι) =>
    independentSourceCovariantWord L A (fun t _ Y => f t Y u) m.val α t 0 Y
  let F := fun (m : Fin (n + 1)) (α : DerivativeWord2 m.val) (u : ι) z =>
    W m α u • c m.val α t z Y v u
  have hF m α u : Continuous (F m α u) := by
    have hc : Continuous (fun z => c m.val α t z Y v u) :=
      (((Qc m α u).regular t).comp₂ contDiff_id (contDiff_const (c := Y))).continuous
    exact hc.const_smul (W m α u)
  have he : (fun z => independentLiftApplySource n c L A f v t z Y) =
      fun z => ∑ m : Fin (n + 1), ∑ α : DerivativeWord2 m.val, ∑ u : ι, F m α u z := by
    funext z
    unfold independentLiftApplySource
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro u _
    rw [independent_covariant_word_fast_independent L A (fun t Y => f t Y u) m.val α t z 0 Y]
    exact mul_comm _ _
  rw [he, fieldCellMean_sum Finset.univ (fun m _ =>
    continuous_finsetSum _ (fun α _ => continuous_finsetSum _ (fun u _ => hF m α u)))]
  apply Finset.sum_eq_zero
  intro m _
  rw [fieldCellMean_sum Finset.univ (fun α _ => continuous_finsetSum _ (fun u _ => hF m α u))]
  apply Finset.sum_eq_zero
  intro α _
  rw [fieldCellMean_sum Finset.univ (fun u _ => hF m α u)]
  apply Finset.sum_eq_zero
  intro u _
  change fieldCellMean (fun z => W m α u • c m.val α t z Y v u) = 0
  rw [fieldCellMean_smul, hmean, smul_zero]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Genuine independent source quotients have higher budgets independent of the parameter point and increment. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def IndependentParameterSourceReserve.quotientHigherSourceData {Hs : ℕ}
    {f : ℝ → Vec 2 → P → ℂ} {F : ℝ → Vec 2 → P → ComplexCellVector}
    (Qf : IndependentParameterSourceReserve Hs f) (QF : IndependentParameterSourceReserve Hs F)
    (K : ℕ) (hK : K + 1 ≤ Hs) (a b : ℝ) (Y w : P) (hw : ‖w‖ ≤ 1)
    (h : ℝ) (hh : h ≠ 0) :
    HigherSourceCarrierData (Set.Icc a b) K
      (h⁻¹ • ((fun t => cellQ0 (fun z => f t z (Y + h • w))) -
        (fun t => cellQ0 (fun z => f t z Y))))
      (h⁻¹ • ((fun t z => F t z (Y + h • w)) - (fun t z => F t z Y))) := by
  let L := independentDirectionPlane w
  have hL : ‖L‖ ≤ 1 := (independentDirectionPlane_norm_le w).trans hw
  let Qs := (Qf.restrictOrder (K + 1) hK).affineSlice L hL Y
  let Qt := (QF.restrictOrder (K + 1) hK).affineSlice L hL Y
  let Q := Qs.quotientHigherSourceData Qt a b 0 (basisVec (0 : Fin 2)) h hh
  have hphase : L (h • basisVec (0 : Fin 2)) + Y = Y + h • w := by
    rw [independentDirectionPlane_basis_smul, add_comm]
  exact Q.congrSources
    (by funext t z; simp only [Pi.smul_apply, Pi.sub_apply, zero_add, map_zero, hphase])
    (by funext t z; simp only [Pi.smul_apply, Pi.sub_apply, zero_add, map_zero, hphase])

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Piola sampling at zero slow displacement keeps the full stored and fast parameter weight. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem native_independent_piola_zero_sampling_jet_bound
    (K : P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun Z : P × Vec 2 => K Z.1 Z.2 a b))
    (E : ℝ) (hE : 0 < E) (N n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (X : P) (hKC : ∀ a b j, j ≤ N →
      ‖iteratedFDeriv ℝ j (fun Z : P × Vec 2 => K Z.1 (E • Z.2) a b) (X, 0)‖ ≤ C)
    (I A : List (Fin 2)) (hA : A.length ≤ I.length) (hn : n + I.length ≤ N)
    (B : P → ℝ) (hB : ContDiff ℝ (n : ℕ∞) B) (θ MB : ℝ)
    (hBj : ∀ j ≤ n, ‖iteratedFDeriv ℝ j B X‖ ≤ θ * MB) (a i : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun Y : P =>
      K Y 0 a i * B Y * transitionT (K Y) I A 0) X‖ ≤
      θ * (((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C * MB *
        (E⁻¹ ^ (I.length - A.length) * (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ I.length)) := by
  let Q : (P × Vec 2) →L[ℝ] P := ContinuousLinearMap.fst ℝ _ _
  let L : P →L[ℝ] (P × Vec 2) := ContinuousLinearMap.inl ℝ _ _
  have hQ : ‖Q‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro Y
    change ‖Y.1‖ ≤ 1 * ‖Y‖
    simpa only [one_mul] using norm_fst_le Y
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro Y
    change ‖(Y, (0 : Vec 2))‖ ≤ 1 * ‖Y‖
    simp only [one_mul, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
    exact le_rfl
  let F := fun Z : P × Vec 2 => K Z.1 (E • Z.2) a i * B Z.1 *
    transitionT (K Z.1) I A (E • Z.2)
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun Z : P × Vec 2 => (Z.1, E • Z.2)) :=
    contDiff_fst.prodMk (contDiff_snd.const_smul E)
  have hF : ContDiff ℝ (n : ℕ∞) F :=
    ((((hK a i).comp hmap).of_le (by simp)).mul (hB.comp Q.contDiff)).mul
      (((transitionT_independent_slow_smooth K hK I A).comp hmap).of_le (by simp))
  have he : (fun Y : P => K Y 0 a i * B Y * transitionT (K Y) I A 0) =
      fun Y => F (L Y + 0) := by
    funext Y
    simp only [F, L, add_zero, ContinuousLinearMap.inl_apply, smul_zero]
  rw [he]
  have hh := finite_affine_derivative_norm_le F n hF L hL 0 X
  simp only [add_zero] at hh ⊢
  apply hh.trans
  have hb' (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDeriv ℝ j (fun Z : P × Vec 2 => B Z.1) (X, 0)‖ ≤ θ * MB := by
    have hp := finite_affine_derivative_norm_le B j (hB.of_le (by exact_mod_cast hj)) Q hQ 0 (X, 0)
    simp only [add_zero] at hp
    exact hp.trans (hBj j hj)
  have hp := native_independent_slow_piola_summand_local_jet_bound K hK E hE N C hC
    (X, 0) hKC I A hA n hn (fun Z : P × Vec 2 => B Z.1) (hB.comp Q.contDiff)
    (θ * MB) hb' a i
  exact hp.trans_eq (by ring)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The independent centered return map is the literal native return for every child phase. -/

variable {P : Type*}

theorem childCenterReturn_eq_independentCenteredReturn (g : P → ChainGeom) (p : P)
    (hg : ChainGeometry.InvLaw (g p)) (anchor ρ θ : ℝ) (hρ : ρ ≠ 0)
    (c : ChainChild) (C H : Vec 2) (hc : c.center = ρ • C) :
    (ρ * θ)⁻¹ • childCenterReturn (g p) anchor c ((ρ * θ) • H) =
      independentCenteredReturn
        (fun Y : P × Vec 2 => centeredGeometryChartInv (g Y.1) ρ anchor Y.2)
        (fun Y : P × Vec 2 => centeredGeometryChart (g Y.1) ρ anchor Y.2)
        θ (p, C, H) :=
  childCenterReturn_parent_scale (g p) hg anchor ρ θ hρ c C H hc

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Genuine mixed primitive reserves produce higher fast source carriers of coordinate words. -/

variable {d H : ℕ}

def coordinateWordHigherSourceData
    {f : ℝ → Vec 2 → Vec d → ℂ} {F : ℝ → Vec 2 → Vec d → ComplexCellVector}
    (Qf : IndependentParameterSourceReserve H f) (QF : IndependentParameterSourceReserve H F)
    (w : List (Fin d)) (K : ℕ) (hK : K + w.length ≤ H) (a b : ℝ) (Y : Vec d) :
    HigherSourceCarrierData (Icc a b) K (fun t => cellQ0 (coordinateSourceWord f w Y t))
      (coordinateSourceWord F w Y) :=
  (Qf.wordJet w.length K (by omega) (coordinateWordDirections w) (coordinateWordDirections_norm w)).higherSourceData
    (QF.wordJet w.length K (by omega) (coordinateWordDirections w) (coordinateWordDirections_norm w)) a b Y

theorem coordinateWordHigherSourceData_scalar_budget
    {f : ℝ → Vec 2 → Vec d → ℂ} {F : ℝ → Vec 2 → Vec d → ComplexCellVector}
    (Qf : IndependentParameterSourceReserve H f) (QF : IndependentParameterSourceReserve H F)
    (w : List (Fin d)) (K : ℕ) (hK : K + w.length ≤ H) (a b : ℝ) (Y : Vec d) :
    (coordinateWordHigherSourceData Qf QF w K hK a b Y).Ns =
      ∑ j : JetIndex2 K, 2 * Qf.budget (w.length + j.1.val) := rfl

theorem coordinateWordHigherSourceData_flux_budget
    {f : ℝ → Vec 2 → Vec d → ℂ} {F : ℝ → Vec 2 → Vec d → ComplexCellVector}
    (Qf : IndependentParameterSourceReserve H f) (QF : IndependentParameterSourceReserve H F)
    (w : List (Fin d)) (K : ℕ) (hK : K + w.length ≤ H) (a b : ℝ) (Y : Vec d) :
    (coordinateWordHigherSourceData Qf QF w K hK a b Y).Nf =
      ∑ j : JetIndex2 K, QF.budget (w.length + j.1.val) := rfl

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Literal finite covariant polynomial coefficients on the full independent parameter space. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def independentCovariantCoefficientStep (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ)
    (η : ℝ) (k : Fin 2) (F : ℕ → ℝ → Vec 2 → P → E)
    (j : ℕ) (t : ℝ) (z : Vec 2) (Y : P) : E :=
  fderiv ℝ (fun y => F j t y Y) z (basisVec k) +
    if j = 0 then 0 else Real.sqrt η • independentSourceCovariantSlow L A k (F (j - 1)) t z Y

def independentCovariantListCoefficients (L : Vec 2 →L[ℝ] P) (A : Vec 2 →L[ℝ] ℝ)
    (η : ℝ) (w : List (Fin 2)) (f : ℝ → Vec 2 → P → E) : ℕ → ℝ → Vec 2 → P → E :=
  w.foldl (fun F k => independentCovariantCoefficientStep L A η k F)
    (fun j => if j = 0 then f else fun _ _ _ => 0)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem independentCovariantListCoefficients_nil (L : Vec 2 →L[ℝ] P)
    (A : Vec 2 →L[ℝ] ℝ) (η : ℝ) (f : ℝ → Vec 2 → P → E) :
    independentCovariantListCoefficients L A η [] f =
      fun j => if j = 0 then f else fun _ _ _ => 0 := rfl

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem independentCovariantListCoefficients_append_singleton (L : Vec 2 →L[ℝ] P)
    (A : Vec 2 →L[ℝ] ℝ) (η : ℝ) (w : List (Fin 2)) (k : Fin 2)
    (f : ℝ → Vec 2 → P → E) :
    independentCovariantListCoefficients L A η (w ++ [k]) f =
      independentCovariantCoefficientStep L A η k
        (independentCovariantListCoefficients L A η w f) := by
  simp only [independentCovariantListCoefficients, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

def independentCovariantStepReserve (H : ℕ) (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1)
    (A : Vec 2 →L[ℝ] ℝ) (η : ℝ) (F : ℕ → ℝ → Vec 2 → P → E) (k : Fin 2) (j : ℕ)
    (QF : ∀ i, IndependentParameterSourceReserve (H + 1) (F i)) :
    IndependentParameterSourceReserve H (independentCovariantCoefficientStep L A η k F j) := by
  by_cases hj : j = 0
  · have he : independentCovariantCoefficientStep L A η k F j =
        fun t z Y => fderiv ℝ (fun y => F j t y Y) z (basisVec k) := by
      funext t z Y
      simp only [independentCovariantCoefficientStep, hj, ite_true, add_zero]
    exact ((QF j).fastPartial H (by omega) k).congrSource he.symm
  · have he : independentCovariantCoefficientStep L A η k F j =
        fun t z Y => fderiv ℝ (fun y => F j t y Y) z (basisVec k) +
          (Real.sqrt η • ContinuousLinearMap.id ℝ E)
            (independentSourceCovariantSlow L A k (F (j - 1)) t z Y) := by
      funext t z Y
      simp only [independentCovariantCoefficientStep, ite_eq_right hj,
        smul_apply, ContinuousLinearMap.id_apply]
    exact (((QF j).fastPartial H (by omega) k).add
      (((QF (j - 1)).covariantSlow H (by omega) L hL A k).map
        (Real.sqrt η • ContinuousLinearMap.id ℝ E))).congrSource he.symm

def IndependentParameterSourceReserve.covariantList {H : ℕ} {f : ℝ → Vec 2 → P → E}
    (Q : IndependentParameterSourceReserve H f) (R : ℕ)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (w : List (Fin 2)) (hR : w.length + R ≤ H) (j : ℕ) :
    IndependentParameterSourceReserve R (independentCovariantListCoefficients L A η w f j) := by
  induction w using List.reverseRecOn generalizing R j with
  | nil =>
    by_cases hj : j = 0
    · have he : f = independentCovariantListCoefficients L A η [] f j := by
        simp only [independentCovariantListCoefficients_nil, hj, ite_true]
      exact (Q.restrictOrder R (by simpa using hR)).congrSource he
    · have he : (fun (_ : ℝ) (_ : Vec 2) (_ : P) => (0 : E)) =
          independentCovariantListCoefficients L A η [] f j := by
        simp only [independentCovariantListCoefficients_nil, ite_eq_right hj]
      exact (IndependentParameterSourceReserve.zero R).congrSource he
  | append_singleton w k ih =>
    exact (independentCovariantStepReserve R L hL A η _ k j
      (fun i => ih (R + 1) (by simp only [List.length_append, List.length_singleton] at hR; omega) i)).congrSource
        (congrFun (independentCovariantListCoefficients_append_singleton L A η w k f) j).symm

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! The literal finite Piola array retains all lowering powers and its single recorded source weight. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem independent_transported_coefficient_zero_jet_bound
    (K : P → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun Z : P × Vec 2 => K Z.1 Z.2 a b))
    (E : ℝ) (hE : 0 < E) (N Dγ n r : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hn : n + Dγ ≤ N) (X : P)
    (hKC : ∀ a b j, j ≤ N →
      ‖iteratedFDeriv ℝ j (fun Z : P × Vec 2 => K Z.1 (E • Z.2) a b) (X, 0)‖ ≤ C)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → P → Vec 2)
    (hB : ∀ d I i, ContDiff ℝ (n : ℕ∞) (fun Y => B d I Y i)) (θ : ℝ)
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ)
    (hBj : ∀ d ∈ Finset.Icc (r + 1) Dγ, ∀ I i j, j ≤ n →
      ‖iteratedFDeriv ℝ j (fun Y => B d I Y i) X‖ ≤ θ * MB d I)
    (A : DerivativeWord2 r) (a : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun Y : P =>
      transportedCoeff (K Y) Dγ (fun d I => B d I Y) r A 0 a) X‖ ≤
      θ * ∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
        ((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C * MB d I *
          (E⁻¹ ^ (d - 1 - r) * (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ (d - 1)) := by
  let f := fun d (I : DerivativeWord2 (d - 1)) (i : Fin 2) (Y : P) =>
    K Y 0 a i * B d I Y i * transitionT (K Y) (List.ofFn I) (List.ofFn A) 0
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun Y : P => (Y, (0 : Vec 2))) :=
    contDiff_id.prodMk contDiff_const
  have hf d I i : ContDiff ℝ (n : ℕ∞) (f d I i) :=
    ((((hK a i).comp hmap).of_le (by simp)).mul (hB d I i)).mul
      (((transitionT_independent_slow_smooth K hK (List.ofFn I) (List.ofFn A)).comp hmap).of_le (by simp))
  have hfi d I : ContDiff ℝ (n : ℕ∞) (fun Y => ∑ i, f d I i Y) :=
    ContDiff.sum (fun i _ => hf d I i)
  have hfd d : ContDiff ℝ (n : ℕ∞) (fun Y => ∑ I, ∑ i, f d I i Y) :=
    ContDiff.sum (fun I _ => hfi d I)
  change ‖iteratedFDeriv ℝ n
    (fun Y => ∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I, ∑ i, f d I i Y) X‖ ≤ _
  apply (CycleJointProofs.finite_jet_finset_sum_norm_le _ _ n (fun d _ => hfd d) X).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  apply (CycleJointProofs.finite_jet_sum_norm_le _ n (hfi d) X).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I _
  apply (CycleJointProofs.finite_jet_sum_norm_le _ n (hf d I) X).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hd' := Finset.mem_Icc.mp hd
  have hh := native_independent_piola_zero_sampling_jet_bound K hK E hE N n C hC X hKC
    (List.ofFn I) (List.ofFn A) (by simp only [List.length_ofFn]; omega)
    (by simp only [List.length_ofFn]; omega) (fun Y => B d I Y i) (hB d I i)
    θ (MB d I) (hBj d hd I i) a i
  simpa only [List.length_ofFn] using hh

end AVRegularity.EntryWeakProofs
end
