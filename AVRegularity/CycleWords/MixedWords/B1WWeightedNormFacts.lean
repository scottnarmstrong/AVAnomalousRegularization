-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.B1WH3Abstract

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords.Assembly

/-! # The poorly buffered case: the trivial fast class

When the block is poorly buffered, the error budget of the word fibre facts is at least the crude
bound, and the abstract fibre word is instantiated with the trivial fast class `Adm = {0}` and
`ν = ‖·‖`. Then:

* the fast stages vanish (`fastRaw_trivial`);
* H4 holds with zero adjoint curves (`b1w_trivial_H4`, the zero curve is a genuine adjoint curve,
  `zero_adjoint_curve`), with `κ' = 0`, `φ' = 0` and no error;
* H3s holds with `κ' = 0`, `φ' = 0` as soon as `ε_s` dominates the tested sources
  (`b1w_trivial_H3s`). That domination is the crude pass. -/

/-- The homogeneous dual derivative vanishes at `0`. -/
theorem cellDualDerivative_zero (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) :
    cellDualDerivative C hG V hv hb t 0 0 0 = 0 := by
  have h := cellDualDerivative_sub_zero C hG V hv hb t 0 0
  rw [sub_self, sub_self] at h
  exact h.symm

/-- **The zero curve is a genuine adjoint curve.** -/
theorem zero_adjoint_curve (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (a b : ℝ) :
    CellWeakHilbertCurve a b (fun _ => 0) (fun _ => 0)
      (fun r => -cellDualDerivative C hG V hv hb r 0 0 0) where
  trace := continuousOn_const
  state := memLp_const _
  dual := by
    simp only [cellDualDerivative_zero, neg_zero]
    exact memLp_const _
  agrees := Filter.Eventually.of_forall fun _ => (map_zero _).symm
  increment := fun _ _ _ _ _ _ => by simp [cellDualDerivative_zero]

/-- The test functional vanishes at the zero test. -/
theorem cellComplexSource_zero_test (θ : Fin 2 → ℂ) (S : ComplexCellL2)
    (F : Fin 2 → ComplexCellL2) : cellComplexSource θ S F 0 = 0 := by
  simp [cellComplexSource, cellComplexPair_zero_right]

section Stages

variable {I : Type*} [Fintype I]

/-- **The fast stages of the trivial class vanish.** -/
theorem fastRaw_trivial (st : I → ℕ) (k : ℕ) (W : I → ComplexCellL2) :
    fastRaw st k W (fun ψ => ψ = 0) (fun ψ => ‖ψ‖) = 0 := by
  unfold fastRaw
  have hset : {y | ∃ ψ : I → ComplexCellL2, (∀ i ∈ stageSet st k, ψ i = 0) ∧
      Real.sqrt (∑ i ∈ stageSet st k, ‖ψ i‖ ^ 2) ≤ 1 ∧
      y = ‖∑ i ∈ stageSet st k, cellComplexPair (W i) (ψ i)‖} = {0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ψ, hψ, -, rfl⟩
      rw [Finset.sum_eq_zero fun i hi => by rw [hψ i hi, cellComplexPair_zero_right], norm_zero]
    · rintro rfl
      refine ⟨0, fun _ _ => rfl, ?_, ?_⟩
      · simp
      · simp [cellComplexPair_zero_right]
  rw [hset, csSup_singleton]

/-- **H3s for the trivial class**, when `ε_s` dominates the tested sources. -/
theorem b1w_trivial_H3s (st : I → ℕ) (M : ℕ) (C : CellCoefficients)
    (W : I → ℝ → ComplexCellL2) (Sr : I → ℝ → ComplexCellL2)
    (F : I → ℝ → Fin 2 → ComplexCellL2) (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ)
    (N₀ : ℂ) (Γ : ℝ → ℝ) (Θ ζ : ℝ) (εs : ℕ → ℝ) (a b : ℝ) (hΘ : 0 ≤ Θ) (hζ : 0 ≤ ζ)
    (hΓ : ∀ r, 0 < Γ r)
    (hsrc : ∀ r ∈ Set.Icc a b, ∀ k < M, ∀ β : I → ℂ,
      ‖∑ i ∈ stageSet st k, β i * cellComplexSource C.θ (Sr i r) (F i r) (qs r)‖ ≤
        ‖N₀‖ * εs k * stageNorm st k β) :
    ∀ r ∈ Set.Icc a b, ∀ k < M, ∀ β : I → ℂ, ∃ κ' : I → ℂ, ∃ φ' : I → ComplexCellL2,
      (∀ k' < k, ∀ i' ∈ stageSet st k', (fun (_ : ℕ) (_ : ℝ) (ψ : ComplexCellL2) => ψ = 0)
        k' r (φ' i')) ∧
      (∀ k' < k, stageNorm st k' κ' ≤ Θ * ζ ^ 2 * stageNorm st k β) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k',
        (fun (_ : ℕ) (ψ : ComplexCellL2) => ‖ψ‖) k' (φ' i') ^ 2) ≤
        Θ * ζ * (‖N₀‖ * Γ r) * stageNorm st k β) ∧
      ‖∑ i ∈ stageSet st k, β i * cellComplexSource C.θ (Sr i r) (F i r) (qs r) -
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
          (κ' i' * cellComplexPair (W i' r) (q r) + cellComplexPair (W i' r) (φ' i'))‖ ≤
        ‖N₀‖ * εs k * stageNorm st k β := by
  intro r hr k hk β
  have hs0 : ∀ k', stageNorm st k' (0 : I → ℂ) = 0 := fun k' => by simp [stageNorm]
  have hnn : 0 ≤ stageNorm st k β := Real.sqrt_nonneg _
  refine ⟨0, 0, fun _ _ _ _ => rfl, fun k' _ => ?_, fun k' _ => ?_, ?_⟩
  · rw [hs0]
    positivity
  · simp only [Pi.zero_apply, norm_zero]
    have : 0 ≤ Θ * ζ * (‖N₀‖ * Γ r) * stageNorm st k β := by
      have := (hΓ r).le
      positivity
    simpa using this
  · simp only [Pi.zero_apply, zero_mul, zero_add, cellComplexPair_zero_right,
      Finset.sum_const_zero, sub_zero]
    exact hsrc r hr k hk β

/-- **H4 for the trivial class**: zero adjoint curves, no error. -/
theorem b1w_trivial_H4 (st : I → ℕ) (M : ℕ) (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : IsCellDrift C.v) (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (W : I → ℝ → ComplexCellL2) (Sr : I → ℝ → ComplexCellL2)
    (F : I → ℝ → Fin 2 → ComplexCellL2) (q : ℝ → ComplexCellL2)
    (N₀ : ℂ) (Γ : ℝ → ℝ) (Θ ζ Cf : ℝ) (εf : ℕ → ℝ) (a b : ℝ) (hΘ : 0 ≤ Θ) (hζ : 0 ≤ ζ)
    (hCf : 0 ≤ Cf) (hΓ : ∀ r, 0 < Γ r) (hεf : ∀ k, 0 ≤ εf k) :
    ∀ t ∈ Set.Icc 0 (b - a), ∀ k < M, ∀ ψ : I → ComplexCellL2,
      (∀ i ∈ stageSet st k, (fun (_ : ℕ) (_ : ℝ) (ψ : ComplexCellL2) => ψ = 0) k (a + t) (ψ i)) →
      Real.sqrt (∑ i ∈ stageSet st k,
        (fun (_ : ℕ) (ψ : ComplexCellL2) => ‖ψ‖) k (ψ i) ^ 2) ≤ 1 →
      ∃ (Ψv : I → ℝ → ComplexCellL2) (Ψs : I → ℝ → TorusHk 1 ℂ),
        (∀ i ∈ stageSet st k, CellWeakHilbertCurve a (a + t) (Ψv i) (Ψs i) (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs i r) 0 0) ∧ Ψv i (a + t) = ψ i) ∧
        (∀ i ∈ stageSet st k,
          (fun (_ : ℕ) (_ : ℝ) (ψ : ComplexCellL2) => ψ = 0) k a (Ψv i a)) ∧
        Real.sqrt (∑ i ∈ stageSet st k,
          (fun (_ : ℕ) (ψ : ComplexCellL2) => ‖ψ‖) k (Ψv i a) ^ 2) ≤
          Cf * Real.exp (-(Real.pi ^ 2 / 8) * t) ∧
        ∀ r ∈ Set.Icc a (a + t), ∃ κ' : I → ℂ, ∃ φ' : I → ComplexCellL2,
          (∀ k' < k, ∀ i' ∈ stageSet st k',
            (fun (_ : ℕ) (_ : ℝ) (ψ : ComplexCellL2) => ψ = 0) k' r (φ' i')) ∧
          (∀ k' < k, stageNorm st k' κ' ≤
            Θ * ζ * Cf * Real.exp (-(Real.pi ^ 2 / 8) * (a + t - r)) / (‖N₀‖ * Γ r)) ∧
          (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k',
            (fun (_ : ℕ) (ψ : ComplexCellL2) => ‖ψ‖) k' (φ' i') ^ 2) ≤
            Θ * Cf * Real.exp (-(Real.pi ^ 2 / 8) * (a + t - r))) ∧
          ‖∑ i ∈ stageSet st k, cellComplexSource C.θ (Sr i r) (F i r) (Ψs i r) -
            ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
              (κ' i' * cellComplexPair (W i' r) (q r) + cellComplexPair (W i' r) (φ' i'))‖ ≤
            εf k / Γ (a + t) := by
  intro t _ k _ ψ hψ _
  refine ⟨fun _ _ => 0, fun _ _ => 0, fun i hi => ⟨?_, (hψ i hi).symm⟩, fun _ _ => rfl, ?_,
    fun r _ => ⟨0, 0, fun _ _ _ _ => rfl, fun k' _ => ?_, fun k' _ => ?_, ?_⟩⟩
  · exact zero_adjoint_curve (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
      (cellDrift_neg_bound hb) a (a + t)
  · simp only [norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
      Real.sqrt_zero]
    positivity
  · have h0 : stageNorm st k' (0 : I → ℂ) = 0 := by simp [stageNorm]
    rw [h0]
    have := (hΓ r).le
    positivity
  · simp only [Pi.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
      Real.sqrt_zero]
    positivity
  · simp only [cellComplexSource_zero_test, Finset.sum_const_zero, Pi.zero_apply, zero_mul,
      zero_add, cellComplexPair_zero_right, sub_self, norm_zero]
    have := hΓ (a + t)
    have := hεf k
    positivity

end Stages

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The adjoint test families of `H4`

H4 tests the stage sources against the adjoint curves `Ψ_i` from admissible tests `ψ_i` at a time
`T` (the crude adjoint, `b1w_crude_adjoint`). The block decomposition at a time `r`
(`b1w_blocks_at`) needs the slice of `Ψ_i` at `r` to be represented in `H^{s_k}`. The adjoint
curves are admissible at every `r ∈ [a, T]`, so they have such representatives `U_i(r)`; an `H^s`
class is determined by its value (`TorusHk.ext_value`), so the test norm is the norm of the
representative (`b1wNu_eq`), and the slices can be replaced by the truncations of the `U_i(r)`
without changing the curve (they agree a.e., `CellWeakHilbertCurve.congr_state_dual`). So
(`b1w_adjoint_family`) the slices are represented in `H^{s_k}` at every `r ∈ [a, T]`, with the
crude decay `‖U_i(r)‖ ≤ C_a e^{-π²/8 (T - r)} ν(ψ_i)`. -/

/-- **The test norm is the norm of the representative**: an `H^s` class is determined by its
value. -/
theorem b1wNu_eq (s : ℕ → ℕ) (k : ℕ) {ψ : ComplexCellL2} (U : TorusHk (s k) ℂ)
    (hU : torusHkValueCLM U = ψ) : b1wNu s k ψ = ‖U‖ := by
  refine le_antisymm (b1wNu_le s k U hU) (le_csInf ⟨‖U‖, U, hU, rfl⟩ ?_)
  rintro x ⟨U', hU', rfl⟩
  have he : U' = U := TorusHk.ext_value (by
    change torusHkValueCLM U' = torusHkValueCLM U
    rw [hU', hU])
  rw [he]

/-- **The adjoint test family of H4, with represented slices.** -/
theorem b1w_adjoint_family {I : Type*} [Fintype I] (st : I → ℕ) (s : ℕ → ℕ) (k : ℕ)
    (hs : 1 ≤ s k) (tr : ℝ → ComplexCellL2) (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : IsCellDrift C.v) (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (a T Ca : ℝ)
    (hadj : ∀ ψ : ComplexCellL2, b1wAdm s tr k T ψ →
      ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve a T Ψv Ψs (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
        Ψv T = ψ ∧
        ∀ r ∈ Icc a T, b1wAdm s tr k r (Ψv r) ∧
          b1wNu s k (Ψv r) ≤ Ca * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) * b1wNu s k ψ)
    (ψ : I → ComplexCellL2) (hψ : ∀ i ∈ stageSet st k, b1wAdm s tr k T (ψ i)) :
    ∃ (Ψv : I → ℝ → ComplexCellL2) (Ψs : I → ℝ → TorusHk 1 ℂ) (U : I → ℝ → TorusHk (s k) ℂ),
      (∀ i, CellWeakHilbertCurve a T (Ψv i) (Ψs i) (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs i r) 0 0)) ∧
      (∀ i ∈ stageSet st k, Ψv i T = ψ i) ∧
      (∀ i, ∀ r ∈ Icc a T, torusHkValueCLM (Ψs i r) = torusHkValueCLM (U i r)) ∧
      ∀ i ∈ stageSet st k, ∀ r ∈ Icc a T, b1wAdm s tr k r (Ψv i r) ∧
        b1wNu s k (Ψv i r) = ‖U i r‖ ∧
        ‖U i r‖ ≤ Ca * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) * b1wNu s k (ψ i) := by
  classical
  -- the tests off the stage are `0`
  have hψ' : ∀ i, b1wAdm s tr k T (if i ∈ stageSet st k then ψ i else 0) := fun i => by
    split_ifs with hi
    · exact hψ i hi
    · exact ⟨⟨0, map_zero _⟩, cellComplexPair_zero_right _⟩
  choose Ψv Ψs hcurve hT hdec using fun i => hadj _ (hψ' i)
  -- the representatives of the slices
  have hrep : ∀ i r, ∃ U : TorusHk (s k) ℂ, r ∈ Icc a T → torusHkValueCLM U = Ψv i r :=
    fun i r => by
      by_cases hr : r ∈ Icc a T
      · obtain ⟨U, hU⟩ := (hdec i r hr).1.1
        exact ⟨U, fun _ => hU⟩
      · exact ⟨0, fun h => absurd h hr⟩
  choose U hU using hrep
  -- the new slices agree a.e. with the old ones
  have hslice : ∀ i, Ψs i =ᵐ[volume.restrict (Icc a T)]
      fun r => if r ∈ Icc a T then truncateTorusHk hs (U i r) else Ψs i r := fun i => by
    filter_upwards [(hcurve i).agrees, ae_restrict_mem measurableSet_Icc] with r hag hr
    simp only [hr, ite_true]
    apply TorusHk.ext_value
    change torusHkValueCLM (Ψs i r) = torusHkValueCLM (truncateTorusHk hs (U i r))
    rw [torusHigher_truncate_value, hU i r hr, hag]
  refine ⟨Ψv, fun i r => if r ∈ Icc a T then truncateTorusHk hs (U i r) else Ψs i r, U,
    fun i => ?_, fun i hi => ?_, fun i r hr => ?_, fun i hi r hr => ?_⟩
  · refine (hcurve i).congr_state_dual (hslice i) ?_
    filter_upwards [hslice i] with r hr
    exact congrArg (fun z => -cellDualDerivative (cellAdjointCoefficients C) hG V
      (cellDrift_neg hv).1 (cellDrift_neg_bound hb) r z 0 0) hr
  · rw [hT i]
    simp only [hi, ite_true]
  · dsimp only
    simp only [hr, ite_true]
    rw [torusHigher_truncate_value]
  · have hν := b1wNu_eq s k (U i r) (hU i r hr)
    refine ⟨(hdec i r hr).1, hν, ?_⟩
    rw [← hν]
    simpa only [hi, ite_true] using (hdec i r hr).2

/-! # Sharp pass: facts on the activity-weighted test norm

A fact on `b1wNuW`, used by the sharp H3s and H4: the bound through an `H^{s_k}` realization `P`
of the transverse projection, `ν ≤ ‖PU‖ + Ω‖U − PU‖` for every representative `U`
(`b1wNuW_le_proj`). -/

section
variable (s : ℕ → ℕ) (Ω : ℕ → ℝ → ℝ) (e : ℝ → Fin 2) (k : ℕ) (r : ℝ)

/-- **The bound through a realization of the transverse projection.** -/
theorem b1wNuW_le_proj (hΩ : 0 ≤ Ω k r) (P : TorusHk (s k) ℂ →L[ℝ] TorusHk (s k) ℂ)
    (hP : ∀ U, torusHkValueCLM (P U) = cellTransverseProjection (e r) (torusHkValueCLM U))
    {ψ : ComplexCellL2} (U : TorusHk (s k) ℂ) (hU : torusHkValueCLM U = ψ) :
    b1wNuW s Ω e k r ψ ≤ ‖P U‖ + Ω k r * ‖U - P U‖ := by
  refine b1wNuW_le s Ω e k r hΩ (P U) (U - P U) (by rw [add_sub_cancel, hU]) ?_
  rw [hP, cellTransverseProjection_idempotent]
end

end AVRegularity.CycleWords.Assembly
end
