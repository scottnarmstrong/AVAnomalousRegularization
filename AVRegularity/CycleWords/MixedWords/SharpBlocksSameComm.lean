-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.B1WCrudeH4
public import AVRegularity.CycleWords.MixedWords.TransformBoundSameOps

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # B1.W sharp pass (weighted norm): the adjoint test family of H4

The weighted analogue of `b1w_adjoint_family`. Per test, the weighted adjoint curves
(`b1w_weighted_adjoint`) bound every curve value through any weighted splitting of the datum. The
weighted norm `n_i = ν_k(T)(ψ_i)` is the infimum over the splittings. The representatives
`U_i(r)` of the curve values are unique (`TorusHk.ext_value`), so the bounds pass to the infimum
(`le_mul_sInf_of_forall`):
* sizes: `√∑‖U_i(r)‖² ≤ C_d e^{-π²(T−r)/8} √∑ n_i²`;
* weighted defects: `ω √∑‖U_i(r) − PU_i(r)‖² ≤ 2C_d e^{-π²(T−r)/8} √∑ n_i²`, for every allowed
  output weight `ω ≥ 1` at `r` and every realization `P` of the projection for `e(r)`
  (`b1w_weighted_family`). -/

/-- A bound by every element of a set bounded below passes to its infimum. -/
theorem le_mul_sInf_of_forall {S : Set ℝ} (hS : S.Nonempty) {f c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ S, f ≤ c * x) : f ≤ c * sInf S := by
  rcases hc.lt_or_eq with hc | hc
  · rw [← div_le_iff₀' hc]
    exact le_csInf hS fun x hx => (div_le_iff₀' hc).2 (h x hx)
  · obtain ⟨x, hx⟩ := hS
    have := h x hx
    rw [← hc, zero_mul] at this ⊢
    exact this

/-- `√∑(ω f_i)² = ω √∑ f_i²` for `ω ≥ 0`. -/
theorem sqrt_sum_mul_sq {α : Type*} (S : Finset α) (f : α → ℝ) {ω : ℝ} (hω : 0 ≤ ω) :
    Real.sqrt (∑ i ∈ S, (ω * f i) ^ 2) = ω * Real.sqrt (∑ i ∈ S, f i ^ 2) := by
  have hsum : ∑ i ∈ S, (ω * f i) ^ 2 = ω ^ 2 * ∑ i ∈ S, f i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hω]

/-- One splitting of one curve value: its size. -/
theorem weighted_split_size {n : ℕ} (U VT VN : TorusHk n ℂ) (hUe : U = VT + VN) {ω X : ℝ}
    (hω : 1 ≤ ω) (hVn : ‖VT‖ + ω * ‖VN‖ ≤ X) : ‖U‖ ≤ X := by
  have h1 : ‖VN‖ ≤ ω * ‖VN‖ := le_mul_of_one_le_left (norm_nonneg _) hω
  rw [hUe]
  exact (norm_add_le _ _).trans (by linarith)

/-- One splitting of one curve value: its size and its weighted defect. -/
theorem weighted_split_bounds {n : ℕ} (e : Fin 2) (U VT VN : TorusHk n ℂ)
    (P : TorusHk n ℂ →L[ℝ] TorusHk n ℂ)
    (hP : ∀ W, torusHkValueCLM (P W) = cellTransverseProjection e (torusHkValueCLM W))
    (hPn : ∀ W, ‖P W‖ ≤ ‖W‖) (hUe : U = VT + VN)
    (hVT : cellTransverseProjection e (torusHkValueCLM VT) = torusHkValueCLM VT) {ω X : ℝ}
    (hω : 1 ≤ ω) (hVn : ‖VT‖ + ω * ‖VN‖ ≤ X) :
    ‖U‖ ≤ X ∧ ω * ‖U - P U‖ ≤ 2 * X := by
  have hPT : P VT = VT := by
    apply TorusHk.ext_value
    change torusHkValueCLM (P VT) = torusHkValueCLM VT
    rw [hP, hVT]
  have hd : U - P U = VN - P VN := by
    rw [hUe, map_add, hPT]
    abel
  have hdn : ‖U - P U‖ ≤ 2 * ‖VN‖ := by
    rw [hd]
    exact (norm_sub_le _ _).trans (by linarith [hPn VN])
  have h1 : ‖VN‖ ≤ ω * ‖VN‖ := le_mul_of_one_le_left (norm_nonneg _) hω
  have h3 : ω * ‖U - P U‖ ≤ ω * (2 * ‖VN‖) := mul_le_mul_of_nonneg_left hdn (by linarith)
  refine ⟨?_, ?_⟩
  · rw [hUe]
    exact (norm_add_le _ _).trans (by linarith)
  · linarith [norm_nonneg VT]

/-- **The weighted adjoint test family of H4.** -/
theorem b1w_weighted_family {I : Type*} [Fintype I] (st : I → ℕ) (s : ℕ → ℕ) (k : ℕ)
    (hs : 1 ≤ s k) (tr : ℝ → ComplexCellL2) (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : IsCellDrift C.v) (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (a T Cd Ωin : ℝ)
    (hCd : 0 ≤ Cd) (e : ℝ → Fin 2) (Ws : ℝ → Set ℝ)
    (hWs : ∀ r, ∀ ω ∈ Ws r, 1 ≤ ω) (hWne : ∀ r, (Ws r).Nonempty)
    (hadj : ∀ ψ : ComplexCellL2, b1wAdm s tr k T ψ →
      ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve a T Ψv Ψs (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
        Ψv T = ψ ∧
        (∀ r ∈ Icc a T, b1wAdm s tr k r (Ψv r)) ∧
        ∀ UT UN : TorusHk (s k) ℂ, torusHkValueCLM (UT + UN) = ψ →
          cellTransverseProjection (e T) (torusHkValueCLM UT) = torusHkValueCLM UT →
        ∀ r ∈ Icc a T, ∀ ω ∈ Ws r, ∃ VT VN : TorusHk (s k) ℂ,
          torusHkValueCLM (VT + VN) = Ψv r ∧
          cellTransverseProjection (e r) (torusHkValueCLM VT) = torusHkValueCLM VT ∧
          ‖VT‖ + ω * ‖VN‖ ≤ Cd * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) * (‖UT‖ + Ωin * ‖UN‖))
    (ψ : I → ComplexCellL2) (hψ : ∀ i ∈ stageSet st k, b1wAdm s tr k T (ψ i)) :
    ∃ (Ψv : I → ℝ → ComplexCellL2) (Ψs : I → ℝ → TorusHk 1 ℂ) (U : I → ℝ → TorusHk (s k) ℂ),
      (∀ i, CellWeakHilbertCurve a T (Ψv i) (Ψs i) (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs i r) 0 0)) ∧
      (∀ i ∈ stageSet st k, Ψv i T = ψ i) ∧
      (∀ i, ∀ r ∈ Icc a T, torusHkValueCLM (Ψs i r) = torusHkValueCLM (U i r)) ∧
      (∀ i ∈ stageSet st k, ∀ r ∈ Icc a T, b1wAdm s tr k r (Ψv i r) ∧
        torusHkValueCLM (U i r) = Ψv i r) ∧
      (∀ r ∈ Icc a T, Real.sqrt (∑ i ∈ stageSet st k, ‖U i r‖ ^ 2) ≤
        Cd * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) *
          Real.sqrt (∑ i ∈ stageSet st k, b1wNuW s (fun _ _ => Ωin) e k T (ψ i) ^ 2)) ∧
      ∀ r ∈ Icc a T, ∀ ω ∈ Ws r, ∀ P : TorusHk (s k) ℂ →L[ℝ] TorusHk (s k) ℂ,
        (∀ W, torusHkValueCLM (P W) = cellTransverseProjection (e r) (torusHkValueCLM W)) →
        (∀ W, ‖P W‖ ≤ ‖W‖) →
        ω * Real.sqrt (∑ i ∈ stageSet st k, ‖U i r - P (U i r)‖ ^ 2) ≤
          2 * Cd * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) *
            Real.sqrt (∑ i ∈ stageSet st k, b1wNuW s (fun _ _ => Ωin) e k T (ψ i) ^ 2) := by
  classical
  -- the tests off the stage are `0`
  have hψ' : ∀ i, b1wAdm s tr k T (if i ∈ stageSet st k then ψ i else 0) := fun i => by
    split_ifs with hi
    · exact hψ i hi
    · exact ⟨⟨0, map_zero _⟩, cellComplexPair_zero_right _⟩
  choose Ψv Ψs hcurve hT hadm hsplit using fun i => hadj _ (hψ' i)
  -- the representatives of the slices
  have hrep : ∀ i r, ∃ U : TorusHk (s k) ℂ, r ∈ Icc a T → torusHkValueCLM U = Ψv i r :=
    fun i r => by
      by_cases hr : r ∈ Icc a T
      · obtain ⟨U, hU⟩ := (hadm i r hr).1
        exact ⟨U, fun _ => hU⟩
      · exact ⟨0, fun h => absurd h hr⟩
  choose U hU using hrep
  have hslice : ∀ i, Ψs i =ᵐ[volume.restrict (Icc a T)]
      fun r => if r ∈ Icc a T then truncateTorusHk hs (U i r) else Ψs i r := fun i => by
    filter_upwards [(hcurve i).agrees, ae_restrict_mem measurableSet_Icc] with r hag hr
    simp only [hr, ite_true]
    apply TorusHk.ext_value
    change torusHkValueCLM (Ψs i r) = torusHkValueCLM (truncateTorusHk hs (U i r))
    rw [torusHigher_truncate_value, hU i r hr, hag]
  -- the bounds for one member, through any splitting of its datum
  have hone : ∀ i ∈ stageSet st k, ∀ r ∈ Icc a T,
      ‖U i r‖ ≤ Cd * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) *
        b1wNuW s (fun _ _ => Ωin) e k T (ψ i) ∧
      ∀ ω ∈ Ws r, ∀ P : TorusHk (s k) ℂ →L[ℝ] TorusHk (s k) ℂ,
        (∀ W, torusHkValueCLM (P W) = cellTransverseProjection (e r) (torusHkValueCLM W)) →
        (∀ W, ‖P W‖ ≤ ‖W‖) →
        ω * ‖U i r - P (U i r)‖ ≤ 2 * Cd * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) *
          b1wNuW s (fun _ _ => Ωin) e k T (ψ i) := by
    intro i hi r hr
    have hψi : (if i ∈ stageSet st k then ψ i else 0) = ψ i := by simp only [hi, ite_true]
    have hc : 0 ≤ Cd * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) :=
      mul_nonneg hCd (Real.exp_pos _).le
    obtain ⟨U₀, hU₀⟩ := (hψ i hi).1
    have hne : ({x : ℝ | ∃ UT UN : TorusHk (s k) ℂ, torusHkValueCLM (UT + UN) = ψ i ∧
        cellTransverseProjection (e T) (torusHkValueCLM UT) = torusHkValueCLM UT ∧
        ‖UT‖ + (fun _ _ => Ωin) k T * ‖UN‖ = x}).Nonempty :=
      ⟨_, 0, U₀, by rw [zero_add, hU₀], by rw [map_zero, map_zero], rfl⟩
    -- one splitting at a time
    have hsplit' : ∀ UT UN : TorusHk (s k) ℂ, torusHkValueCLM (UT + UN) = ψ i →
        cellTransverseProjection (e T) (torusHkValueCLM UT) = torusHkValueCLM UT →
        ∀ ω ∈ Ws r, ∃ VT VN : TorusHk (s k) ℂ, U i r = VT + VN ∧
          cellTransverseProjection (e r) (torusHkValueCLM VT) = torusHkValueCLM VT ∧
          ‖VT‖ + ω * ‖VN‖ ≤ Cd * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) *
            (‖UT‖ + Ωin * ‖UN‖) := by
      intro UT UN hUv hUT ω hω
      obtain ⟨VT, VN, hVv, hVT, hVn⟩ := hsplit i UT UN (by rw [hψi]; exact hUv) hUT r hr ω hω
      refine ⟨VT, VN, ?_, hVT, hVn⟩
      apply TorusHk.ext_value
      change torusHkValueCLM (U i r) = torusHkValueCLM (VT + VN)
      rw [hU i r hr, hVv]
    refine ⟨le_mul_sInf_of_forall hne hc ?_, fun ω hω P hP hPn => ?_⟩
    · rintro x ⟨UT, UN, hUv, hUT, rfl⟩
      obtain ⟨ω₀, hω₀⟩ := hWne r
      obtain ⟨VT, VN, hUe, -, hVn⟩ := hsplit' UT UN hUv hUT ω₀ hω₀
      exact weighted_split_size (U i r) VT VN hUe (hWs r ω₀ hω₀) hVn
    · have h2c : 0 ≤ 2 * Cd * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) := by linarith
      have hgoal : ω * ‖U i r - P (U i r)‖ ≤ (2 * Cd * Real.exp (-(Real.pi ^ 2 / 8) * (T - r))) *
          b1wNuW s (fun _ _ => Ωin) e k T (ψ i) := by
        refine le_mul_sInf_of_forall hne h2c ?_
        rintro x ⟨UT, UN, hUv, hUT, rfl⟩
        obtain ⟨VT, VN, hUe, hVT, hVn⟩ := hsplit' UT UN hUv hUT ω hω
        have := (weighted_split_bounds (e r) (U i r) VT VN P hP hPn hUe hVT (hWs r ω hω)
          hVn).2
        linarith
      exact hgoal
  refine ⟨Ψv, fun i r => if r ∈ Icc a T then truncateTorusHk hs (U i r) else Ψs i r, U,
    fun i => ?_, fun i hi => ?_, fun i r hr => ?_, fun i hi r hr => ⟨?_, hU i r hr⟩,
    fun r hr => ?_, fun r hr ω hω P hP hPn => ?_⟩
  · refine (hcurve i).congr_state_dual (hslice i) ?_
    filter_upwards [hslice i] with r hr
    exact congrArg (fun z => -cellDualDerivative (cellAdjointCoefficients C) hG V
      (cellDrift_neg hv).1 (cellDrift_neg_bound hb) r z 0 0) hr
  · rw [hT i]
    simp only [hi, ite_true]
  · dsimp only
    simp only [hr, ite_true]
    rw [torusHigher_truncate_value]
  · exact hadm i r hr
  · exact sqrt_sum_sq_le_mul _ _ _ (mul_nonneg hCd (Real.exp_pos _).le)
      (fun _ _ => norm_nonneg _) fun i hi => (hone i hi r hr).1
  · have hω0 : 0 ≤ ω := (zero_le_one).trans (hWs r ω hω)
    have h := sqrt_sum_sq_le_mul (stageSet st k) (fun i => ω * ‖U i r - P (U i r)‖)
      (fun i => b1wNuW s (fun _ _ => Ωin) e k T (ψ i))
      (c := 2 * Cd * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)))
      (by have := mul_nonneg hCd (Real.exp_pos (-(Real.pi ^ 2 / 8) * (T - r))).le; linarith)
      (fun i _ => mul_nonneg hω0 (norm_nonneg _)) fun i hi => (hone i hi r hr).2 ω hω P hP hPn
    rwa [sqrt_sum_mul_sq _ (fun i => ‖U i r - P (U i r)‖) hω0] at h

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # the sharp same-level pair operators

`T = sameOp` with the drift multiplier bounded through the jets of `√η v`, so that
`ϖ ‖v‖ ≤ S^{-1/2} C`.  Norm, slow-test norm and slow-test pairing are proved here. -/

universe u v

theorem sameOp_trunc (n N : ℕ) (hnN : n + 1 ≤ N) (θ : Vec 2)
    (M : Fin 2 → TorusHk n ℂ →L[ℝ] TorusHk n ℂ) (a4 a5 : Fin 2 → ℝ) (e123 e4 e5 : ℝ)
    (ψ : TorusHk N ℂ) :
    sameOp n N hnN θ M a4 a5 e123 e4 e5 ψ =
      sameOp n (n + 1) le_rfl θ M a4 a5 e123 e4 e5 (truncateTorusHk hnN ψ) := rfl

theorem sameOp_sharp_norm (n N : ℕ) (hnN : n + 1 ≤ N) (θ : Vec 2)
    (M : Fin 2 → TorusHk n ℂ →L[ℝ] TorusHk n ℂ) (a4 a5 : Fin 2 → ℝ) (e123 e4 e5 : ℝ)
    (B ρ : ℝ) (hB : 0 ≤ B) (hMB : ∀ c U, ‖M c U‖ ≤ B * ‖U‖)
    (ha4 : ∀ k, |a4 k| ≤ 4) (ha5 : ∀ k, |a5 k| ≤ 4) (hθ : ∀ k, |θ k| ≤ ρ) (ψ : TorusHk N ℂ)
    (b : ℝ) (hb : ‖truncateTorusHk hnN ψ‖ ≤ b) :
    ‖sameOp n N hnN θ M a4 a5 e123 e4 e5 ψ‖ ≤
      (|e123| + |e4| * (B + 8 * (1 + ρ)) + |e5| * (B + 8 * (1 + ρ))) * b := by
  rw [sameOp_trunc]
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
  refine (sameOp_norm_le n (n + 1) le_rfl θ M a4 a5 e123 e4 e5 B ρ hB hMB ha4 ha5 hθ _).trans ?_
  refine mul_le_mul_of_nonneg_left hb ?_
  have : 0 ≤ B + 8 * (1 + ρ) := by positivity
  positivity

theorem mean_of_ae_const (U : ComplexCellL2) (c : ℂ)
    (h : (U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] fun _ => c) :
    cellMeanCLM U = c := by
  have : U = cellConstantCLM c := Lp.ext (h.trans (cellConstantCLM_ae c).symm)
  rw [this]
  exact cellMeanCLM_constant c

theorem mean_const_hk (K : ℕ) (E : ℂ) :
    cellMeanCLM (torusHkValueCLM (torusHigherConstant K E)) = E := by
  rw [torusHigherConstant_value]
  exact cellMeanCLM_constant E

theorem mean_twist_const (n : ℕ) (θ : Vec 2) (k : Fin 2) (E : ℂ) :
    cellMeanCLM (torusHkValueCLM (tbTwist n θ k (torusHigherConstant (n + 1) E))) =
      Complex.I * (θ k : ℂ) * E := by
  apply mean_of_ae_const
  have hv : (torusHkValueCLM (torusHigherConstant (n + 1) E) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun _ => E := by
    rw [torusHigherConstant_value]; exact cellConstantCLM_ae E
  filter_upwards [tbTwist_value_ae n θ k (torusHigherConstant (n + 1) E) (fun _ => E)
    contDiff_const hv] with x hx
  rw [hx]
  simp [fibreCovDeriv]

theorem mean_mul_const (n : ℕ) (E : ℂ) (w : Vec 2 → ℝ) (hw : cellMean (fun x => (w x : ℂ)) = 0)
    (U : TorusHk n ℂ)
    (hU : (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (w x : ℂ) * E) : cellMeanCLM (torusHkValueCLM U) = 0 := by
  rw [cellMeanCLM_apply]
  unfold cellMean at hw ⊢
  rw [integral_congr_ae hU, integral_mul_const, hw, zero_mul]

theorem sameOp_mean_const (n N : ℕ) (hnN : n + 1 ≤ N) (θ : Vec 2)
    (M : Fin 2 → TorusHk n ℂ →L[ℝ] TorusHk n ℂ) (a4 a5 : Fin 2 → ℝ) (e123 e4 e5 : ℝ)
    (w : Fin 2 → Vec 2 → ℝ) (hw : ∀ c, cellMean (fun x => (w c x : ℂ)) = 0)
    (hMv : ∀ c U, (torusHkValueCLM (M c U) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => (w c x : ℂ) * torusHkValueCLM U x)
    (E : ℂ) :
    cellMeanCLM (torusHkValueCLM (sameOp n N hnN θ M a4 a5 e123 e4 e5 (torusHigherConstant N E)))
      = (e123 : ℂ) * E + (e4 : ℂ) * ((a4 0 : ℂ) * (Complex.I * (θ 0 : ℂ) * E) +
          (a4 1 : ℂ) * (Complex.I * (θ 1 : ℂ) * E)) +
        (e5 : ℂ) * ((a5 0 : ℂ) * (Complex.I * (θ 0 : ℂ) * E) +
          (a5 1 : ℂ) * (Complex.I * (θ 1 : ℂ) * E)) := by
  have hn : truncateTorusHk (by omega : n ≤ N) (torusHigherConstant N E) =
      torusHigherConstant n E := torusHigherConstant_truncate _ E
  have hn1 : truncateTorusHk hnN (torusHigherConstant N E) = torusHigherConstant (n + 1) E :=
    torusHigherConstant_truncate _ E
  have hM : ∀ c, cellMeanCLM (torusHkValueCLM (M c (torusHigherConstant n E))) = 0 := fun c => by
    refine mean_mul_const n E (w c) (hw c) _ ?_
    filter_upwards [hMv c (torusHigherConstant n E), cellConstantCLM_ae E] with x hx h2
    rw [hx, torusHigherConstant_value, h2]
  simp only [sameOp, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, hn, hn1, map_add, map_smul, hM, mean_const_hk,
    mean_twist_const, Complex.real_smul]
  ring

theorem zeta_inv_le (x S : ℝ) (hx : 0 ≤ x) (hS : 1 ≤ S) :
    (Real.sqrt S)⁻¹ ≤ min 1 (x + (Real.sqrt S)⁻¹) := by
  refine le_min ?_ (by linarith)
  rw [inv_le_one₀ (Real.sqrt_pos.2 (by linarith))]
  rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hS

theorem zeta_x_le (x S ρ : ℝ) (hx : 0 ≤ x) (hxρ : x ≤ ρ) :
    x ≤ (1 + |ρ|) * min 1 (x + (Real.sqrt S)⁻¹) := by
  have hiv : 0 ≤ (Real.sqrt S)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hz0 : 0 ≤ min 1 (x + (Real.sqrt S)⁻¹) := le_min zero_le_one (by linarith)
  rcases min_choice 1 (x + (Real.sqrt S)⁻¹) with h | h
  · rw [h]; nlinarith [le_abs_self ρ, abs_nonneg ρ]
  · rw [h]; nlinarith [abs_nonneg ρ]

theorem varpi_eq (η S : ℝ) (hη : 0 < η) :
    Real.sqrt (η / S) = Real.sqrt η * (Real.sqrt S)⁻¹ := by
  rw [Real.sqrt_div hη.le, div_eq_mul_inv]

theorem varpi_le_zeta (η S x : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hS : 1 ≤ S) (hx : 0 ≤ x) :
    Real.sqrt (η / S) ≤ min 1 (x + (Real.sqrt S)⁻¹) := by
  refine le_trans ?_ (zeta_inv_le x S hx hS)
  rw [varpi_eq η S hη]
  have : Real.sqrt η ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hη1
  exact mul_le_of_le_one_left (inv_nonneg.2 (Real.sqrt_nonneg _)) this

section Coef

variable {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {Nw m : ℕ} {Ks : Fin Nw → ℕ}

open Classical in
theorem sameE123_sharp (al ϖ : ℝ) (hal : |al| ≤ 1)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (h00 : |G 0 0| ≤ 2) (h11 : |G 1 1| ≤ 2)
    (h01 : |G 0 1 + G 1 0| ≤ 4) (i i' : B1WIndex ι h Nw m Ks) :
    |sameE123 al ϖ G i i'| ≤ 8 * ϖ ^ 2 := by
  unfold sameE123
  have hp : |ϖ ^ 2| = ϖ ^ 2 := abs_of_nonneg (sq_nonneg _)
  have b1 := sameE_abs_le al hal i i' (2, 0) (G 0 0 * ϖ ^ (2 + 0))
  have b2 := sameE_abs_le al hal i i' (1, 1) ((G 0 1 + G 1 0) * ϖ ^ (1 + 1))
  have b3 := sameE_abs_le al hal i i' (0, 2) (G 1 1 * ϖ ^ (0 + 2))
  rw [abs_mul, show (2 + 0 : ℕ) = 2 from rfl, hp] at b1
  rw [abs_mul, show (1 + 1 : ℕ) = 2 from rfl, hp] at b2
  rw [abs_mul, show (0 + 2 : ℕ) = 2 from rfl, hp] at b3
  have c1 := mul_le_mul_of_nonneg_right h00 (sq_nonneg ϖ)
  have c2 := mul_le_mul_of_nonneg_right h01 (sq_nonneg ϖ)
  have c3 := mul_le_mul_of_nonneg_right h11 (sq_nonneg ϖ)
  calc _ ≤ |sameE al i i' (2, 0) (G 0 0 * ϖ ^ (2 + 0)) +
        sameE al i i' (1, 1) ((G 0 1 + G 1 0) * ϖ ^ (1 + 1))| +
        |sameE al i i' (0, 2) (G 1 1 * ϖ ^ (0 + 2))| := abs_add_le _ _
    _ ≤ |sameE al i i' (2, 0) (G 0 0 * ϖ ^ (2 + 0))| +
        |sameE al i i' (1, 1) ((G 0 1 + G 1 0) * ϖ ^ (1 + 1))| +
        |sameE al i i' (0, 2) (G 1 1 * ϖ ^ (0 + 2))| := by gcongr; exact abs_add_le _ _
    _ ≤ 8 * ϖ ^ 2 := by linarith

end Coef

section Construct

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The drift multiplier, bounded through the jets of `√η v` (the case `S = 1` of
`drift_mul_exists`). -/
def sharpSameM (K : ScalarConstants) {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (r : ℝ) (n : ℕ) :
    Fin 2 → TorusHk n ℂ →L[ℝ] TorusHk n ℂ :=
  (drift_mul_exists K (S := 1) (ϖ := Real.sqrt F.η) F.piece.hη le_rfl (by simp) n (F.v r)
    (F.piece.hvs r) (F.piece.hv.2.2.1 r) (fun j z => F.piece.hvj j r z)).choose

theorem sharpSameM_spec (K : ScalarConstants) {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (r : ℝ) (n : ℕ) :
    (∀ c U, ‖sharpSameM K F r n c U‖ ≤ (|cellDriftNativePrice n| *
        ((∑ l ∈ Finset.range (n + 1), |K.Cvj l|) / Real.sqrt F.η)) * ‖U‖) ∧
      ∀ c U, (torusHkValueCLM (sharpSameM K F r n c U) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun x => (F.v r x c : ℂ) * torusHkValueCLM U x :=
  (drift_mul_exists K (S := 1) (ϖ := Real.sqrt F.η) F.piece.hη le_rfl (by simp) n (F.v r)
    (F.piece.hvs r) (F.piece.hv.2.2.1 r) (fun j z => F.piece.hvj j r z)).choose_spec

open Classical in
/-- The sharp same-level pair operator: `sameOp` with the multiplier `sharpSameM`. -/
def sharpSameT (K : ScalarConstants) {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (n N : ℕ) (hnN : n + 1 ≤ N) (i i' : B1WIndex ι h Nw m Ks) :
    TorusHk N ℂ →L[ℝ] TorusHk n ℂ :=
  sameOp n N hnN θ (sharpSameM K F r n) (fun k => F.G r k 0 + F.G r 0 k)
    (fun k => F.G r k 1 + F.G r 1 k)
    (sameE123 (sameAlive F.ηg F.letters i) F.ϖ (F.G r) i i')
    (sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0)))
    (sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1)))


theorem sharpSameT_value (K : ScalarConstants) {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (n N : ℕ) (hnN : n + 1 ≤ N) (h3 : 3 ≤ N) (i i' : B1WIndex ι h Nw m Ks) (ψ : TorusHk N ℂ) :
    (torusHkValueCLM (sharpSameT K F θ r n N hnN i i' ψ) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
        b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
          star (b1wSameTransform θ (F.G r) (F.v r) i i'
            (fun y => star (torusHigherClassicalValue N ψ y)) z) := by
  have hϖpos : 0 < F.ϖ := by
    rw [F.piece.hϖ]; exact Real.sqrt_pos.2 (div_pos F.piece.hη (by linarith [F.piece.hS]))
  have hv := sameOp_value n N hnN h3 θ (sharpSameM K F r n) (F.v r) (sharpSameM_spec K F r n).2
    (fun k => F.G r k 0 + F.G r 0 k) (fun k => F.G r k 1 + F.G r 1 k)
    (sameE123 (sameAlive F.ηg F.letters i) F.ϖ (F.G r) i i')
    (sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0)))
    (sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1))) ψ
  have hf1 : ContDiff ℝ 1 (torusHigherClassicalValue N ψ) := by
    have := torusHigherClassicalValue_contDiff N 1 (by omega) ψ
    exact_mod_cast this
  filter_upwards [hv] with z hz
  unfold sharpSameT
  rw [hz, same_star_eff F.π F.ϖ F.ηg F.letters F.piece.hπ hϖpos.ne' θ (F.G r) (F.v r) i i'
    (torusHigherClassicalValue N ψ) z ((hf1.differentiable one_ne_zero) z)]
  simp only [Fin.sum_univ_two, sameE123]


/-- The constant of the sharp norm bound. -/
def sharpQ (K : ScalarConstants) (n : ℕ) (ρ : ℝ) : ℝ :=
  8 + 2 * (|cellDriftNativePrice n| * ∑ l ∈ Finset.range (n + 1), |K.Cvj l|) + 16 * (1 + |ρ|)

theorem sharpQ_nonneg (K : ScalarConstants) (n : ℕ) (ρ : ℝ) : 0 ≤ sharpQ K n ρ := by
  unfold sharpQ; positivity

open Classical in
theorem sharpSameT_norm (K : ScalarConstants) {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (ρ : ℝ)
    (hρ : fibreNorm (planeFibreFrequency F.η θ) ≤ ρ) (r : ℝ)
    (n N : ℕ) (hnN : n + 1 ≤ N) (i i' : B1WIndex ι h Nw m Ks) (ψ : TorusHk N ℂ) (b : ℝ)
    (hb : ‖truncateTorusHk hnN ψ‖ ≤ b) :
    ‖sharpSameT K F θ r n N hnN i i' ψ‖ ≤ (if SameRel i i' then sharpQ K n ρ *
      min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) else 0) * b := by
  have hη := F.piece.hη
  have hη1 := F.piece.hη1
  have hS := F.piece.hS
  have hϖ := F.piece.hϖ
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  have hs : 0 < Real.sqrt F.η := Real.sqrt_pos.2 hη
  have hϖpos : 0 < F.ϖ := by
    rw [hϖ]; exact Real.sqrt_pos.2 (div_pos hη (by linarith))
  have hϖ1 : F.ϖ ≤ 1 := by
    rw [hϖ, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ((div_le_self hη.le hS).trans hη1)
  have hϖζ : F.ϖ ≤ min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) := by
    rw [hϖ]; exact varpi_le_zeta F.η F.S _ hη hη1 hS hx0
  have hinv := zeta_inv_le (fibreNorm (planeFibreFrequency F.η θ)) F.S hx0 hS
  have hϖeq : F.ϖ = Real.sqrt F.η * (Real.sqrt F.S)⁻¹ := by rw [hϖ, varpi_eq F.η F.S hη]
  have hθ := theta_abs_le hη hη1 θ hρ
  have hρ0 : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
  have hsum : ∀ j k, |F.G r j k + F.G r k j| ≤ 4 := fun j k =>
    metric_sum_le (F.G r) (fun ξ => F.piece.hGm.2.2.2 r 0 ξ) j k
  have hdiag : ∀ j, |F.G r j j| ≤ 2 := by
    intro j
    have := hsum j j
    rw [← two_mul, abs_mul] at this
    norm_num at this
    linarith
  have hal := sameAlive_abs_le F.ηg F.letters i
  generalize min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) = ζ at *
  obtain ⟨hMB, -⟩ := sharpSameM_spec K F r n
  by_cases hrel : SameRel i i'
  · simp only [hrel, ↓reduceIte]
    have hB : 0 ≤ |cellDriftNativePrice n| *
        ((∑ l ∈ Finset.range (n + 1), |K.Cvj l|) / Real.sqrt F.η) :=
      mul_nonneg (abs_nonneg _) (div_nonneg (Finset.sum_nonneg fun l _ => abs_nonneg _) hs.le)
    have hn := sameOp_sharp_norm n N hnN θ (sharpSameM K F r n) (fun k => F.G r k 0 + F.G r 0 k)
      (fun k => F.G r k 1 + F.G r 1 k)
      (sameE123 (sameAlive F.ηg F.letters i) F.ϖ (F.G r) i i')
      (sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0)))
      (sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1)))
      _ ρ hB hMB (fun k => hsum k 0) (fun k => hsum k 1) hθ ψ b hb
    have h123 := sameE123_sharp (sameAlive F.ηg F.letters i) F.ϖ hal (F.G r)
      (hdiag 0) (hdiag 1) (hsum 0 1) i i'
    have h4 : |sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0))| ≤ F.ϖ :=
      (sameE_abs_le (sameAlive F.ηg F.letters i) hal i i' (1, 0)
        (1 * F.ϖ ^ (1 + 0))).trans (by simp [abs_of_pos hϖpos])
    have h5 : |sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1))| ≤ F.ϖ :=
      (sameE_abs_le (sameAlive F.ηg F.letters i) hal i i' (0, 1)
        (1 * F.ϖ ^ (0 + 1))).trans (by simp [abs_of_pos hϖpos])
    have hb0 : 0 ≤ b := (norm_nonneg _).trans hb
    refine hn.trans (mul_le_mul_of_nonneg_right ?_ hb0)
    have hq : 0 ≤ |cellDriftNativePrice n| *
        ((∑ l ∈ Finset.range (n + 1), |K.Cvj l|) / Real.sqrt F.η) + 8 * (1 + ρ) := by positivity
    have e4' := mul_le_mul_of_nonneg_right h4 hq
    have e5' := mul_le_mul_of_nonneg_right h5 hq
    have hkey : F.ϖ * (|cellDriftNativePrice n| *
        ((∑ l ∈ Finset.range (n + 1), |K.Cvj l|) / Real.sqrt F.η)) =
        |cellDriftNativePrice n| * (∑ l ∈ Finset.range (n + 1), |K.Cvj l|) *
          (Real.sqrt F.S)⁻¹ := by
      rw [hϖeq]; field_simp
    have hP : 0 ≤ |cellDriftNativePrice n| * ∑ l ∈ Finset.range (n + 1), |K.Cvj l| :=
      mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun l _ => abs_nonneg _)
    have hPz : |cellDriftNativePrice n| * (∑ l ∈ Finset.range (n + 1), |K.Cvj l|) *
        (Real.sqrt F.S)⁻¹ ≤ |cellDriftNativePrice n| *
          (∑ l ∈ Finset.range (n + 1), |K.Cvj l|) * ζ :=
      mul_le_mul_of_nonneg_left hinv hP
    have hϖ2 : F.ϖ ^ 2 ≤ ζ := by nlinarith only [hϖ1, hϖζ, hϖpos]
    have hρ' : ρ ≤ |ρ| := le_abs_self ρ
    unfold sharpQ
    nlinarith only [mul_nonneg (abs_nonneg ρ) (hϖpos.le.trans hϖζ), h123, e4', e5', hkey, hPz, hϖ2,
      hρ', hρ0, hϖpos, hϖζ, hϖ1, hP, hB, hq]
  · simp only [hrel, ↓reduceIte]
    have hb0 : 0 ≤ b := (norm_nonneg _).trans hb
    have hn := sameOp_sharp_norm n N hnN θ (sharpSameM K F r n) (fun k => F.G r k 0 + F.G r 0 k)
      (fun k => F.G r k 1 + F.G r 1 k)
      (sameE123 (sameAlive F.ηg F.letters i) F.ϖ (F.G r) i i')
      (sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0)))
      (sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1)))
      _ ρ (mul_nonneg (abs_nonneg _) (div_nonneg (Finset.sum_nonneg fun l _ => abs_nonneg _)
        hs.le)) hMB (fun k => hsum k 0) (fun k => hsum k 1) hθ ψ b hb
    refine hn.trans (le_of_eq ?_)
    rw [sameE123_eq_zero _ _ _ i i' hrel,
      sameE_eq_zero_of_not_rel _ i i' hrel (1, 0) (by simp [sameShifts]),
      sameE_eq_zero_of_not_rel _ i i' hrel (0, 1) (by simp [sameShifts])]
    simp


/-- The constant of the slow-test norm bound. -/
def sharpC1 (K : ScalarConstants) (n : ℕ) (ρ M₀ : ℝ) : ℝ :=
  sharpQ K n ρ * (‖torusHigherConstant (n + 1) (1 : ℂ)‖ + |M₀| * |ρ|)

theorem sharpC1_nonneg (K : ScalarConstants) (n : ℕ) (ρ M₀ : ℝ) : 0 ≤ sharpC1 K n ρ M₀ := by
  unfold sharpC1
  exact mul_nonneg (sharpQ_nonneg K n ρ) (by positivity)

open Classical in
theorem sharpSameT_slow_norm (K : ScalarConstants) {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (ρ M₀ : ℝ)
    (hρ : fibreNorm (planeFibreFrequency F.η θ) ≤ ρ) (r : ℝ)
    (n N : ℕ) (hnN : n + 1 ≤ N) (i i' : B1WIndex ι h Nw m Ks) (E : ℂ) (Dd : TorusHk N ℂ)
    (hD : ‖Dd‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ) * ‖E‖) :
    ‖sharpSameT K F θ r n N hnN i i' (torusHigherConstant N E + Dd)‖ ≤
      (if SameRel i i' then sharpC1 K n ρ M₀ *
        min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) else 0) * ‖E‖ := by
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  have hb : ‖truncateTorusHk hnN (torusHigherConstant N E + Dd)‖ ≤
      (‖torusHigherConstant (n + 1) (1 : ℂ)‖ + |M₀| * |ρ|) * ‖E‖ := by
    rw [map_add, torusHigherConstant_truncate hnN]
    refine (norm_add_le _ _).trans ?_
    rw [torusHigherConstant_norm]
    have h1 : ‖truncateTorusHk hnN Dd‖ ≤ ‖Dd‖ := truncateTorusHk_norm_le _ _
    have h2 : M₀ * fibreNorm (planeFibreFrequency F.η θ) ≤ |M₀| * |ρ| :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) hx0).trans
        (mul_le_mul_of_nonneg_left (hρ.trans (le_abs_self _)) (abs_nonneg _))
    nlinarith [norm_nonneg E, mul_le_mul_of_nonneg_right h2 (norm_nonneg E)]
  have := sharpSameT_norm K F θ ρ hρ r n N hnN i i' _ _ hb
  refine this.trans (le_of_eq ?_)
  unfold sharpC1
  split_ifs <;> ring


open Classical in
theorem sharpSameT_mean_const (K : ScalarConstants) {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (ρ : ℝ)
    (hρ : fibreNorm (planeFibreFrequency F.η θ) ≤ ρ) (r : ℝ)
    (n N : ℕ) (hnN : n + 1 ≤ N) (i i' : B1WIndex ι h Nw m Ks) (E : ℂ) :
    ‖cellMeanCLM (torusHkValueCLM (sharpSameT K F θ r n N hnN i i' (torusHigherConstant N E)))‖ ≤
      (8 + 16 * (1 + |ρ|)) * min 1 (fibreNorm (planeFibreFrequency F.η θ) +
        (Real.sqrt F.S)⁻¹) ^ 2 * ‖E‖ := by
  have hη := F.piece.hη
  have hη1 := F.piece.hη1
  have hS := F.piece.hS
  have hϖ := F.piece.hϖ
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  have hϖpos : 0 < F.ϖ := by
    rw [hϖ]; exact Real.sqrt_pos.2 (div_pos hη (by linarith))
  have hϖ1 : F.ϖ ≤ 1 := by
    rw [hϖ, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ((div_le_self hη.le hS).trans hη1)
  have hϖζ : F.ϖ ≤ min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) := by
    rw [hϖ]; exact varpi_le_zeta F.η F.S _ hη hη1 hS hx0
  have hxz := zeta_x_le (fibreNorm (planeFibreFrequency F.η θ)) F.S ρ hx0 hρ
  have hθ := theta_abs_le hη hη1 θ (le_refl (fibreNorm (planeFibreFrequency F.η θ)))
  have hsum : ∀ j k, |F.G r j k + F.G r k j| ≤ 4 := fun j k =>
    metric_sum_le (F.G r) (fun ξ => F.piece.hGm.2.2.2 r 0 ξ) j k
  have hdiag : ∀ j, |F.G r j j| ≤ 2 := by
    intro j
    have := hsum j j
    rw [← two_mul, abs_mul] at this
    norm_num at this
    linarith
  have hal := sameAlive_abs_le F.ηg F.letters i
  have h123 := sameE123_sharp (sameAlive F.ηg F.letters i) F.ϖ hal (F.G r)
    (hdiag 0) (hdiag 1) (hsum 0 1) i i'
  have h4 : |sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0))| ≤ F.ϖ :=
    (sameE_abs_le (sameAlive F.ηg F.letters i) hal i i' (1, 0)
      (1 * F.ϖ ^ (1 + 0))).trans (by simp [abs_of_pos hϖpos])
  have h5 : |sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1))| ≤ F.ϖ :=
    (sameE_abs_le (sameAlive F.ηg F.letters i) hal i i' (0, 1)
      (1 * F.ϖ ^ (0 + 1))).trans (by simp [abs_of_pos hϖpos])
  unfold sharpSameT
  rw [sameOp_mean_const n N hnN θ (sharpSameM K F r n) _ _ _ _ _ (fun c x => F.v r x c)
    (fun c => F.piece.hv0 r c) (sharpSameM_spec K F r n).2 E]
  generalize min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) = ζ at *
  generalize fibreNorm (planeFibreFrequency F.η θ) = x at *
  generalize sameE123 (sameAlive F.ηg F.letters i) F.ϖ (F.G r) i i' = e1 at *
  generalize sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0)) = e4 at *
  generalize sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1)) = e5 at *
  have ha : ∀ (a : Fin 2 → ℝ), (∀ k, |a k| ≤ 4) → ∀ e : ℝ, |e| ≤ F.ϖ →
      ‖(e : ℂ) * ((a 0 : ℂ) * (Complex.I * (θ 0 : ℂ) * E) +
        (a 1 : ℂ) * (Complex.I * (θ 1 : ℂ) * E))‖ ≤ 8 * F.ϖ * x * ‖E‖ := by
    intro a ha e he
    have t0 : ‖(a 0 : ℂ) * (Complex.I * (θ 0 : ℂ) * E)‖ ≤ 4 * x * ‖E‖ := by
      simp only [norm_mul, Complex.norm_real, Complex.norm_I, one_mul, Real.norm_eq_abs]
      calc |a 0| * (|θ 0| * ‖E‖) ≤ 4 * (x * ‖E‖) := by
            gcongr
            · exact ha 0
            · exact hθ 0
        _ = _ := by ring
    have t1 : ‖(a 1 : ℂ) * (Complex.I * (θ 1 : ℂ) * E)‖ ≤ 4 * x * ‖E‖ := by
      simp only [norm_mul, Complex.norm_real, Complex.norm_I, one_mul, Real.norm_eq_abs]
      calc |a 1| * (|θ 1| * ‖E‖) ≤ 4 * (x * ‖E‖) := by
            gcongr
            · exact ha 1
            · exact hθ 1
        _ = _ := by ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |e| * ‖_ + _‖ ≤ F.ϖ * (4 * x * ‖E‖ + 4 * x * ‖E‖) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add t0 t1)
      _ = _ := by ring
  have hq4 := ha (fun k => F.G r k 0 + F.G r 0 k) (fun k => hsum k 0) e4 h4
  have hq5 := ha (fun k => F.G r k 1 + F.G r 1 k) (fun k => hsum k 1) e5 h5
  have hE : ‖(e1 : ℂ) * E‖ ≤ 8 * F.ϖ ^ 2 * ‖E‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right h123 (norm_nonneg _)
  beta_reduce at hq4 hq5
  refine norm_add₃_le.trans ?_
  have hz0 : 0 ≤ ζ := hϖpos.le.trans hϖζ
  have hE0 := norm_nonneg E
  have c1 : F.ϖ ^ 2 ≤ ζ ^ 2 := pow_le_pow_left₀ hϖpos.le hϖζ 2
  have c2 : F.ϖ * x ≤ ζ * ((1 + |ρ|) * ζ) := mul_le_mul hϖζ hxz hx0 hz0
  have : 8 * F.ϖ ^ 2 * ‖E‖ + 8 * F.ϖ * x * ‖E‖ + 8 * F.ϖ * x * ‖E‖ ≤
      (8 + 16 * (1 + |ρ|)) * ζ ^ 2 * ‖E‖ := by
    nlinarith [mul_nonneg hE0 (sub_nonneg.2 c1), mul_nonneg hE0 (sub_nonneg.2 c2)]
  linarith


/-- The constant of the slow-test pairing bound. -/
def sharpC2 (K : ScalarConstants) (n : ℕ) (ρ M₀ : ℝ) : ℝ :=
  (8 + 16 * (1 + |ρ|)) + sharpQ K n ρ * (|M₀| * (1 + |ρ|)) +
    |M₀| * (1 + |ρ|) * sharpC1 K n ρ M₀

theorem sharpC2_nonneg (K : ScalarConstants) (n : ℕ) (ρ M₀ : ℝ) : 0 ≤ sharpC2 K n ρ M₀ := by
  unfold sharpC2
  have := sharpQ_nonneg K n ρ
  have := sharpC1_nonneg K n ρ M₀
  positivity

open Classical in
theorem sharpSameT_slow_pair (K : ScalarConstants) {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (ρ M₀ : ℝ)
    (hρ : fibreNorm (planeFibreFrequency F.η θ) ≤ ρ) (r : ℝ)
    (n N : ℕ) (hnN : n + 1 ≤ N) (i i' : B1WIndex ι h Nw m Ks) (E : ℂ) (Dd : TorusHk N ℂ)
    (hD : ‖Dd‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ) * ‖E‖)
    (R : ComplexCellL2) (hR : ‖R‖ ≤ |M₀| * fibreNorm (planeFibreFrequency F.η θ)) :
    ‖sharpPair R (sharpSameT K F θ r n N hnN i i' (torusHigherConstant N E + Dd))‖ ≤
      (if SameRel i i' then sharpC2 K n ρ M₀ *
        min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) ^ 2 else 0) * ‖E‖ := by
  have hη := F.piece.hη
  have hη1 := F.piece.hη1
  have hS := F.piece.hS
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  have hslow := sharpSameT_slow_norm K F θ ρ M₀ hρ r n N hnN i i' E Dd hD
  by_cases hrel : SameRel i i'
  · simp only [hrel, ↓reduceIte] at hslow ⊢
    have hxz := zeta_x_le (fibreNorm (planeFibreFrequency F.η θ)) F.S ρ hx0 hρ
    have hz0 : 0 ≤ min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) :=
      le_min zero_le_one (by
        have : 0 ≤ (Real.sqrt F.S)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
        linarith)
    have hmean := sharpSameT_mean_const K F θ ρ hρ r n N hnN i i' E
    have hTD := sharpSameT_norm K F θ ρ hρ r n N hnN i i' Dd _ (le_refl ‖truncateTorusHk hnN Dd‖)
    simp only [hrel, ↓reduceIte] at hTD
    have hDn : ‖truncateTorusHk hnN Dd‖ ≤ ‖Dd‖ := truncateTorusHk_norm_le _ _
    have hQ := sharpQ_nonneg K n ρ
    have hmD : ‖cellMeanCLM (torusHkValueCLM (sharpSameT K F θ r n N hnN i i' Dd))‖ ≤
        ‖sharpSameT K F θ r n N hnN i i' Dd‖ :=
      (cellMeanCLM_norm_le _).trans (sharp_value_norm_le _)
    have hsplit : sharpSameT K F θ r n N hnN i i' (torusHigherConstant N E + Dd) =
        sharpSameT K F θ r n N hnN i i' (torusHigherConstant N E) +
          sharpSameT K F θ r n N hnN i i' Dd := map_add _ _ _
    have hM0 : ‖Dd‖ ≤ |M₀| * fibreNorm (planeFibreFrequency F.η θ) * ‖E‖ :=
      hD.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self _) hx0) (norm_nonneg _))
    refine (sharpPair_le_mean _ _).trans ?_
    have hU : ‖sharpSameT K F θ r n N hnN i i' (torusHigherConstant N E) +
        sharpSameT K F θ r n N hnN i i' Dd‖ ≤
        sharpC1 K n ρ M₀ * min 1 (fibreNorm (planeFibreFrequency F.η θ) +
          (Real.sqrt F.S)⁻¹) * ‖E‖ := by
      rw [← hsplit]; exact hslow
    rw [hsplit, map_add, map_add]
    refine (add_le_add ((norm_add_le _ _).trans (add_le_add hmean hmD)) (mul_le_mul hR
      hU (norm_nonneg _) (by positivity))).trans ?_
    generalize min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) = ζ at *
    generalize fibreNorm (planeFibreFrequency F.η θ) = x at *
    have hC1 := sharpC1_nonneg K n ρ M₀
    have hE0 := norm_nonneg E
    have hA := abs_nonneg M₀
    have hy : |M₀| * x ≤ |M₀| * ((1 + |ρ|) * ζ) := mul_le_mul_of_nonneg_left hxz hA
    have s1 : ‖sharpSameT K F θ r n N hnN i i' Dd‖ ≤
        sharpQ K n ρ * ζ * (|M₀| * ((1 + |ρ|) * ζ) * ‖E‖) := by
      refine hTD.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hQ hz0))
      exact hDn.trans (hM0.trans (mul_le_mul_of_nonneg_right hy hE0))
    have s2 : |M₀| * x * (sharpC1 K n ρ M₀ * ζ * ‖E‖) ≤
        |M₀| * ((1 + |ρ|) * ζ) * (sharpC1 K n ρ M₀ * ζ * ‖E‖) :=
      mul_le_mul_of_nonneg_right hy (by positivity)
    have : (8 + 16 * (1 + |ρ|)) * ζ ^ 2 * ‖E‖ +
        sharpQ K n ρ * ζ * (|M₀| * ((1 + |ρ|) * ζ) * ‖E‖) +
        |M₀| * ((1 + |ρ|) * ζ) * (sharpC1 K n ρ M₀ * ζ * ‖E‖) =
        sharpC2 K n ρ M₀ * ζ ^ 2 * ‖E‖ := by unfold sharpC2; ring
    linarith
  · simp only [hrel, ↓reduceIte] at hslow ⊢
    have h0 : ‖sharpSameT K F θ r n N hnN i i' (torusHigherConstant N E + Dd)‖ = 0 := by
      rw [zero_mul] at hslow
      exact le_antisymm hslow (norm_nonneg _)
    refine (sharpPair_norm_le _ _).trans (le_of_eq ?_)
    rw [h0]
    ring

end Construct

open Classical in
/-- **Transversality.** The sharp same-level operator commutes with the transverse
projection in the least window: the drift is the shear `ext p` (`ext_agree`, `ext_shear`),
invariant along `e_p`, and multiplication by it, the twisted derivatives, the constant metric and
the conjugation commute with the average along `e_p`. -/
def SharpSameCommStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (n : ℕ),
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
  ∀ r ∈ Icc F.a F.b, ∀ (N : ℕ) (hnN : n + 1 ≤ N), (Finset.univ.sup d) + 3 ≤ N →
  ∀ i i' : B1WIndex ι h Nw m Ks,
    ∀ p, IsLeastWindow F.reg p r →
    ∀ (PN : TorusHk N ℂ →L[ℝ] TorusHk N ℂ) (Pn : TorusHk n ℂ →L[ℝ] TorusHk n ℂ),
      (∀ U, torusHkValueCLM (PN U) =
        cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
      (∀ U, torusHkValueCLM (Pn U) =
        cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
      ∀ ψ : TorusHk N ℂ, Pn (sharpSameT K F θ r n N hnN i i' ψ) =
        sharpSameT K F θ r n N hnN i i' (PN ψ)

open Classical in
/-- `SharpSameOpsStatement` from the transversality statement. -/
theorem sharpSameOps_of_comm (hc : SharpSameCommStatement.{u, v}) :
    SharpSameOpsStatement.{u, v} := by
  intro K Nw D m d Ks ρ n M₀
  refine ⟨sharpQ K n ρ + sharpC1 K n ρ M₀ + sharpC2 K n ρ M₀, by
    have := sharpQ_nonneg K n ρ
    have := sharpC1_nonneg K n ρ M₀
    have := sharpC2_nonneg K n ρ M₀
    positivity, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hρ r hr N hnN hdN i i'
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  have hz0 : 0 ≤ min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) :=
    le_min zero_le_one (by
      have : 0 ≤ (Real.sqrt F.S)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
      linarith)
  have hQ := sharpQ_nonneg K n ρ
  have h1 := sharpC1_nonneg K n ρ M₀
  have h2 := sharpC2_nonneg K n ρ M₀
  refine ⟨sharpSameT K F θ r n N hnN i i', sharpSameT_value K F θ r n N hnN (by omega) i i',
    fun ψ => ?_, fun E Dd hD => ?_, fun R hR E Dd hD => ?_, ?_⟩
  · refine (sharpSameT_norm K F θ ρ hρ r n N hnN i i' ψ _ (truncateTorusHk_norm_le _ ψ)).trans ?_
    split_ifs
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hz0)
        (norm_nonneg _)
    · exact le_rfl
  · refine (sharpSameT_slow_norm K F θ ρ M₀ hρ r n N hnN i i' E Dd hD).trans ?_
    split_ifs
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hz0)
        (norm_nonneg _)
    · exact le_rfl
  · refine (sharpSameT_slow_pair K F θ ρ M₀ hρ r n N hnN i i' E Dd hD R hR).trans ?_
    split_ifs
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
        (norm_nonneg _)
    · exact le_rfl
  · intro p hp PN Pn e1 e2 ψ
    exact hc K Nw D m d Ks n g₁ F θ r hr N hnN hdN i i' p hp PN Pn e1 e2 ψ

/-- **The sharp same-level families**, from the transversality statement. -/
theorem sharpSameLevel_of_comm (hc : SharpSameCommStatement.{u, v}) :
    SharpSameLevelStatement.{u, v} :=
  sharpSameLevel_of_ops (sharpSameOps_of_comm hc)

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords AVenhance.Infra.Torus
namespace AVRegularity.CycleWords.Assembly

/-! # the same-level operators commute with the transverse projection in a window

For realizations of the transverse projection on `H^N` and `H^n` (given by their values), the
truncations, the twisted derivatives, and the multiplication by a function invariant along `e`
commute with them.  In the least window the drift is `ext p`, a shear invariant along `e_p`. -/

universe u v

theorem comm_trunc {n N : ℕ} (hnN : n ≤ N) (e : Fin 2)
    (PN : TorusHk N ℂ →L[ℝ] TorusHk N ℂ) (Pn : TorusHk n ℂ →L[ℝ] TorusHk n ℂ)
    (hN : ∀ U, torusHkValueCLM (PN U) = cellTransverseProjection e (torusHkValueCLM U))
    (hn : ∀ U, torusHkValueCLM (Pn U) = cellTransverseProjection e (torusHkValueCLM U))
    (ψ : TorusHk N ℂ) : Pn (truncateTorusHk hnN ψ) = truncateTorusHk hnN (PN ψ) := by
  apply TorusHk.ext_value
  change torusHkValueCLM (Pn (truncateTorusHk hnN ψ)) =
    torusHkValueCLM (truncateTorusHk hnN (PN ψ))
  rw [hn, torusHkValueCLM_truncate, torusHkValueCLM_truncate, hN]

theorem comm_scalar {n : ℕ} (e : Fin 2) (Pn : TorusHk n ℂ →L[ℝ] TorusHk n ℂ)
    (hn : ∀ U, torusHkValueCLM (Pn U) = cellTransverseProjection e (torusHkValueCLM U))
    (c : ℂ) (U : TorusHk n ℂ) :
    Pn (torusHigherScalarCLM n c U) = torusHigherScalarCLM n c (Pn U) := by
  apply TorusHk.ext_value
  change torusHkValueCLM (Pn (torusHigherScalarCLM n c U)) =
    torusHkValueCLM (torusHigherScalarCLM n c (Pn U))
  rw [hn, torusHigherScalarCLM_value, torusHigherScalarCLM_value, hn,
    cellTransverseProjection_scalar]

theorem tbDeriv_value_eq (K : ℕ) (k : Fin 2) (U : TorusHk (K + 1) ℂ) :
    torusHkValueCLM (tbDeriv K k U) =
      cellDerivativeCLM k (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le K)) U) := by
  have hidx : prefixJetIndex (K := K) (r := 1) (fun _ => k) (valueIndex2 K) =
      truncateJetIndex (Nat.succ_le_succ (Nat.zero_le K)) ⟨⟨1, by decide⟩, fun _ => k⟩ := by
    unfold prefixJetIndex truncateJetIndex valueIndex2 valueIndex
    simp
  change U.val (prefixJetIndex (K := K) (r := 1) (fun _ => k) (valueIndex2 K)) =
    U.val (truncateJetIndex (Nat.succ_le_succ (Nat.zero_le K)) ⟨⟨1, by decide⟩, fun _ => k⟩)
  rw [hidx]

theorem comm_deriv (K : ℕ) (e k : Fin 2) (Pn : TorusHk K ℂ →L[ℝ] TorusHk K ℂ)
    (hn : ∀ U, torusHkValueCLM (Pn U) = cellTransverseProjection e (torusHkValueCLM U))
    (W W' : TorusHk (K + 1) ℂ)
    (hW : torusHkValueCLM W' = cellTransverseProjection e (torusHkValueCLM W)) :
    Pn (tbDeriv K k W) = tbDeriv K k W' := by
  apply TorusHk.ext_value
  change torusHkValueCLM (Pn (tbDeriv K k W)) = torusHkValueCLM (tbDeriv K k W')
  have h1 : truncateTorusHk (Nat.succ_le_succ (Nat.zero_le K)) W' =
      cellTransverseH1Projection e (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le K)) W) := by
    apply TorusHk.ext_value
    change torusHkValueCLM (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le K)) W') =
      torusHkValueCLM (cellTransverseH1Projection e _)
    rw [cellTransverseH1Projection_value, torusHkValueCLM_truncate, torusHkValueCLM_truncate, hW]
  rw [hn, tbDeriv_value_eq, tbDeriv_value_eq, h1, cellTransverseH1Projection_derivative]

theorem comm_twist (K : ℕ) (e k : Fin 2) (θ : Vec 2) (Pn : TorusHk K ℂ →L[ℝ] TorusHk K ℂ)
    (hn : ∀ U, torusHkValueCLM (Pn U) = cellTransverseProjection e (torusHkValueCLM U))
    (W W' : TorusHk (K + 1) ℂ)
    (hW : torusHkValueCLM W' = cellTransverseProjection e (torusHkValueCLM W)) :
    Pn (tbTwist K θ k W) = tbTwist K θ k W' := by
  have hT : ∀ (c : ℂ), Pn (torusHigherScalarCLM K c (tbTrunc K W)) =
      torusHigherScalarCLM K c (tbTrunc K W') := by
    intro c
    rw [comm_scalar e Pn hn]
    congr 1
    apply TorusHk.ext_value
    change torusHkValueCLM (Pn (tbTrunc K W)) = torusHkValueCLM (tbTrunc K W')
    rw [hn]
    change cellTransverseProjection e (torusHkValueCLM (truncateTorusHk _ W)) =
      torusHkValueCLM (truncateTorusHk _ W')
    rw [torusHkValueCLM_truncate, torusHkValueCLM_truncate, hW]
  unfold tbTwist
  rw [add_apply, add_apply, map_add, comm_deriv K e k Pn hn W W' hW]
  exact congrArg _ (hT _)

theorem comm_mul {n : ℕ} (e : Fin 2) (Pn : TorusHk n ℂ →L[ℝ] TorusHk n ℂ)
    (hn : ∀ U, torusHkValueCLM (Pn U) = cellTransverseProjection e (torusHkValueCLM U))
    (w : Vec 2 → ℝ) (hwc : Continuous w) (hp : AVenhance.IsZ2Periodic w)
    (ht : ∀ (z : Vec 2) (s : ℝ), w (z + s • basisVec e) = w z) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x, |w x| ≤ C) (M' : TorusHk n ℂ →L[ℝ] TorusHk n ℂ)
    (hM : ∀ U, (torusHkValueCLM (M' U) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => (w x : ℂ) * torusHkValueCLM U x)
    (U U' : TorusHk n ℂ)
    (hU : torusHkValueCLM U' = cellTransverseProjection e (torusHkValueCLM U)) :
    Pn (M' U) = M' U' := by
  have hc : Measurable (fun x => (w x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hwc.measurable
  have hper : IsZdPeriodic (fun x => (w x : ℂ)) :=
    (isZdPeriodic_iff_frozen _).mpr (fun m z => congrArg (fun y : ℝ => (y : ℂ)) (hp m z))
  have hm := hc.aestronglyMeasurable (μ := volume.restrict AVenhance.unitCube)
  have hb' : ∀ x, ‖(fun x => (w x : ℂ)) x‖ ≤ C := fun x => by
    simpa [Complex.norm_real] using hb x
  have ht' : ∀ (z : Vec 2) (s : ℝ), (fun x => (w x : ℂ)) (z + s • basisVec e) =
      (fun x => (w x : ℂ)) z := fun z s => congrArg (fun y : ℝ => (y : ℂ)) (ht z s)
  have hX : ∀ V : TorusHk n ℂ, torusHkValueCLM (M' V) =
      cellCoefficientCLM (fun x => (w x : ℂ)) hm C hC hb' (torusHkValueCLM V) := fun V =>
    Lp.ext ((hM V).trans (cellCoefficientCLM_ae _ _ _ _ _ _).symm)
  apply TorusHk.ext_value
  change torusHkValueCLM (Pn (M' U)) = torusHkValueCLM (M' U')
  rw [hn, hX, hX, hU, cellTransverseProjection_coefficient e _ hc hper ht' hm C hC hb']

theorem comm_sameOp (n N : ℕ) (hnN : n + 1 ≤ N) (θ : Vec 2) (e : Fin 2)
    (M : Fin 2 → TorusHk n ℂ →L[ℝ] TorusHk n ℂ) (a4 a5 : Fin 2 → ℝ) (e123 e4 e5 : ℝ)
    (PN : TorusHk N ℂ →L[ℝ] TorusHk N ℂ) (Pn : TorusHk n ℂ →L[ℝ] TorusHk n ℂ)
    (hN : ∀ U, torusHkValueCLM (PN U) = cellTransverseProjection e (torusHkValueCLM U))
    (hn : ∀ U, torusHkValueCLM (Pn U) = cellTransverseProjection e (torusHkValueCLM U))
    (hMc : ∀ c (U U' : TorusHk n ℂ),
      torusHkValueCLM U' = cellTransverseProjection e (torusHkValueCLM U) →
      Pn (M c U) = M c U') (ψ : TorusHk N ℂ) :
    Pn (sameOp n N hnN θ M a4 a5 e123 e4 e5 ψ) =
      sameOp n N hnN θ M a4 a5 e123 e4 e5 (PN ψ) := by
  have h0 := comm_trunc (by omega : n ≤ N) e PN Pn hN hn ψ
  have hU : ∀ (L : ℕ) (h : L ≤ N), torusHkValueCLM (truncateTorusHk h (PN ψ)) =
      cellTransverseProjection e (torusHkValueCLM (truncateTorusHk h ψ)) := fun L h => by
    rw [torusHkValueCLM_truncate, torusHkValueCLM_truncate, hN]
  have hM := fun c => hMc c _ _ (hU n (by omega))
  have hT := fun k => comm_twist n e k θ Pn hn _ _ (hU (n + 1) hnN)
  simp only [sameOp, add_apply, smul_apply, ContinuousLinearMap.comp_apply, map_add, map_smul,
    h0, hM, hT]

open Classical in
/-- **The transversality step.** -/
theorem sharpSameComm : SharpSameCommStatement.{u, v} := by
  intro K Nw D m d Ks n g₁ ι _ h _ _ _ _ _ _ F θ r hr N hnN hdN i i' p hp PN Pn hN hn ψ
  have hwin : r ∈ Icc (F.reg.lo p - F.reg.buffer) (F.reg.hi p + F.reg.buffer) :=
    ⟨by linarith [hp.1.1, F.pkg.buffer_nonneg], by linarith [hp.1.2, F.pkg.buffer_nonneg]⟩
  have hinv : ∀ (z : Vec 2) (s : ℝ), F.v r (z + s • basisVec (F.reg.orient p)) = F.v r z := by
    intro z s
    rw [← F.pkg.ext_agree p r hwin, ← F.pkg.ext_agree p r hwin]
    obtain ⟨V, hV⟩ := F.pkg.ext_shear p
    exact shear_drift_parallel_invariant (F.pkg.ext p) (F.reg.orient p) V hV r z s
  obtain ⟨M0, hM0⟩ := F.piece.hv.2.1
  unfold sharpSameT
  refine comm_sameOp n N hnN θ (F.reg.orient p) _ _ _ _ _ _ PN Pn hN hn
    (fun c U U' hU => ?_) ψ
  have hcont : Continuous (fun x => F.v r x c) :=
    (continuous_apply c).comp (F.piece.hvs r).continuous
  have hper : AVenhance.IsZ2Periodic (fun x => F.v r x c) := by
    intro k x
    simp only [F.piece.hv.2.2.1 r k x]
  have hb : ∀ x, |F.v r x c| ≤ |M0| := by
    intro x
    have h1 : F.v r x c ^ 2 ≤ ∑ j, F.v r x j ^ 2 :=
      Finset.single_le_sum (f := fun j => F.v r x j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ c)
    exact sq_le_sq.1 (h1.trans (hM0 r x))
  exact comm_mul (F.reg.orient p) Pn hn (fun x => F.v r x c) hcont hper
    (fun z s => by simp only [hinv z s]) |M0| (abs_nonneg _) hb
    (sharpSameM K F r n c) ((sharpSameM_spec K F r n).2 c) U U' hU

/-- **The sharp same-level families.** -/
theorem sharpSameLevel : SharpSameLevelStatement.{u, v} :=
  sharpSameLevel_of_comm sharpSameComm

end AVRegularity.CycleWords.Assembly
end
