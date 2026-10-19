-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.B1WData
import AVRegularity.CycleWords.MixedWords.B1WRepresentation
import AVRegularity.CoupledEnergy.Galerkin.PlainVariationalEnergy
public import AVRegularity.CycleWords.MixedWords.TransformBoundLetterTermOp
public import AVRegularity.CycleWords.MixedWords.TransformBoundSameOps

section
@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Discard

/-! # the plain pass, abstract form

Forced stage curves `W_i` of one cell equation. The tested sources of the stages of order `k`
against adjoint curves are represented, at almost every time, by the earlier stages tested
against families of size `B` (`hrep`). The adjoint curves from `H^{s_k}` tests have `H^{s_k}`
representatives of size `C_a κ(r,t)` (`hadj`), for a kernel with `κ(a,r)κ(r,t) ≤ Aκ(a,t)`.

`plain_pass`: then every stage of order `k` tested at time `t` is at most
`C_k (1 + (t − a))^k κ(a,t) ‖W(a)‖ ‖ψ‖`, with `C_k = C_a + A B C_a ∑_{k'<k} C_{k'}`.

The proof is a strong induction on `k`, with no Gronwall step: the forcing of the stages of
order `k` involves only the earlier orders. The step is one exact duality
`⟨W(t), ψ⟩ = ⟨W(a), Ψ(a)⟩ + ∫_a^t ∑ src(Ψ)` (`cellWeakAdjointPairing_forced`). -/

section
open AVRegularity.CycleWords.Assembly

/-- The constants of the plain pass. -/
def plainConst (Ca A B : ℝ) : ℕ → ℝ
  | k => Ca + A * B * Ca * ∑ k' : Fin k, plainConst Ca A B k'
termination_by k => k
decreasing_by exact k'.isLt

theorem plainConst_eq (Ca A B : ℝ) (k : ℕ) :
    plainConst Ca A B k = Ca + A * B * Ca * ∑ k' ∈ Finset.range k, plainConst Ca A B k' := by
  rw [plainConst, Finset.sum_range]

theorem plainConst_nonneg {Ca A B : ℝ} (hCa : 0 ≤ Ca) (hA : 0 ≤ A) (hB : 0 ≤ B) (k : ℕ) :
    0 ≤ plainConst Ca A B k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [plainConst_eq]
    have : 0 ≤ ∑ k' ∈ Finset.range k, plainConst Ca A B k' :=
      Finset.sum_nonneg fun k' hk' => ih k' (Finset.mem_range.1 hk')
    positivity

/-- The bound of one earlier order, uniformly in the time of the integral. -/
theorem plain_term_le {Ck' A B Ca X Y kar krt kat T r : ℝ} {k' k : ℕ} (hk : k' < k)
    (hCk' : 0 ≤ Ck') (hB : 0 ≤ B) (hCa : 0 ≤ Ca) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hkar : 0 ≤ kar) (hkrt : 0 ≤ krt) (hmul : kar * krt ≤ A * kat) (hr0 : 0 ≤ r) (hrT : r ≤ T) :
    Ck' * (1 + r) ^ k' * kar * X * (B * (Ca * krt * Y)) ≤
      A * B * Ca * Ck' * (1 + T) ^ (k - 1) * kat * X * Y := by
  have h1 : (1 + r) ^ k' ≤ (1 + T) ^ (k - 1) :=
    (pow_le_pow_left₀ (by linarith) (by linarith) k').trans
      (pow_le_pow_right₀ (by linarith) (by omega))
  have h2 : 0 ≤ (1 + r) ^ k' := pow_nonneg (by linarith) _
  calc Ck' * (1 + r) ^ k' * kar * X * (B * (Ca * krt * Y))
      = (Ck' * B * Ca * X * Y) * ((1 + r) ^ k' * (kar * krt)) := by ring
    _ ≤ (Ck' * B * Ca * X * Y) * ((1 + T) ^ (k - 1) * (A * kat)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul h1 hmul (mul_nonneg hkar hkrt) (pow_nonneg (by linarith) _)
    _ = A * B * Ca * Ck' * (1 + T) ^ (k - 1) * kat * X * Y := by ring

/-- The two parts of the step together. -/
theorem plain_step_le {I0 Iint Ca A B S T kat X Y : ℝ} {k : ℕ} (hS0 : k = 0 → S = 0) (hT : 0 ≤ T)
    (hCa : 0 ≤ Ca) (hkat : 0 ≤ kat) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hS : 0 ≤ S)
    (h0 : I0 ≤ Ca * kat * X * Y)
    (hint : Iint ≤ T * (A * B * Ca * S * (1 + T) ^ (k - 1) * kat * X * Y))
    (hAB : 0 ≤ A * B * Ca) :
    I0 + Iint ≤ (Ca + A * B * Ca * S) * (1 + T) ^ k * kat * X * Y := by
  have hT1 : 1 ≤ (1 + T) ^ k := one_le_pow₀ (by linarith)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · have h0S := hS0 hk
    subst hk
    rw [h0S] at hint ⊢
    have hI : Iint ≤ 0 := by simpa using hint
    simp only [mul_zero, add_zero, pow_zero, mul_one]
    linarith
  have hpow : T * (1 + T) ^ (k - 1) ≤ (1 + T) ^ k := by
    have : (1 + T) ^ k = (1 + T) ^ (k - 1) * (1 + T) := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    have := pow_nonneg (show (0 : ℝ) ≤ 1 + T by linarith) (k - 1)
    nlinarith
  have hP : 0 ≤ kat * X * Y := by positivity
  have hQ : 0 ≤ A * B * Ca * S := mul_nonneg hAB hS
  calc I0 + Iint ≤ Ca * kat * X * Y + T * (A * B * Ca * S * (1 + T) ^ (k - 1) * kat * X * Y) :=
        add_le_add h0 hint
    _ = Ca * (kat * X * Y) + (A * B * Ca * S) * (T * (1 + T) ^ (k - 1)) * (kat * X * Y) := by
        ring
    _ ≤ Ca * (1 + T) ^ k * (kat * X * Y) + (A * B * Ca * S) * (1 + T) ^ k * (kat * X * Y) := by
        refine add_le_add ?_ ?_
        · have := mul_le_mul_of_nonneg_left hT1 hCa
          nlinarith
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hQ) hP
    _ = (Ca + A * B * Ca * S) * (1 + T) ^ k * kat * X * Y := by ring

/-- The pairing of a stage family against representatives. -/
theorem pair_sum_le {I : Type*} (st : Finset I) (univ : Finset I) (hsub : st ⊆ univ) {N : ℕ}
    (w : I → ComplexCellL2) (U : I → TorusHk N ℂ) (v : I → ComplexCellL2)
    (hv : ∀ i ∈ st, v i = torusHkValueCLM (U i)) :
    ‖∑ i ∈ st, cellComplexPair (w i) (v i)‖ ≤
      Real.sqrt (∑ i ∈ univ, ‖w i‖ ^ 2) * Real.sqrt (∑ i ∈ st, ‖U i‖ ^ 2) := by
  calc ‖∑ i ∈ st, cellComplexPair (w i) (v i)‖
      ≤ ∑ i ∈ st, ‖w i‖ * ‖U i‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi =>
          (cellComplexPair_norm_le _ _).trans (mul_le_mul_of_nonneg_left
            (by rw [hv i hi]; exact torusHk_value_norm_le _) (norm_nonneg _)))
    _ ≤ Real.sqrt (∑ i ∈ st, ‖w i‖ ^ 2) * Real.sqrt (∑ i ∈ st, ‖U i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ i ∈ univ, ‖w i‖ ^ 2) * Real.sqrt (∑ i ∈ st, ‖U i‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (Finset.sum_le_sum_of_subset_of_nonneg
          hsub fun i _ _ => sq_nonneg _)) (Real.sqrt_nonneg _)

section Pass

variable {I : Type*} [Fintype I]

/-- **The plain pass, abstract form.** -/
theorem plain_pass (st : I → ℕ) (s : ℕ → ℕ) (M : ℕ) {a b : ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ) (hv : IsCellDrift C.v)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (W : I → ℝ → ComplexCellL2) (Ws : I → ℝ → TorusHk 1 ℂ) (S : I → ℝ → ComplexCellL2)
    (Fl : I → ℝ → Fin 2 → ComplexCellL2)
    (hW : ∀ i, CellWeakHilbertCurve a b (W i) (Ws i) (fun t =>
      cellDualDerivative C hG V hv.1 hb t (Ws i t) (S i t) (Fl i t)))
    (κ : ℝ → ℝ → ℝ) (A Ca B : ℝ) (hκ : ∀ r t, 0 ≤ κ r t)
    (hmul : ∀ r t, a ≤ r → r ≤ t → t ≤ b → κ a r * κ r t ≤ A * κ a t)
    (hA : 0 ≤ A) (hCa : 0 ≤ Ca) (hB : 0 ≤ B)
    (hadj : ∀ k < M, ∀ t ∈ Icc a b, ∀ ψ : I → TorusHk (s k) ℂ,
      ∃ (Ψv : I → ℝ → ComplexCellL2) (Ψs : I → ℝ → TorusHk 1 ℂ)
        (U : I → ℝ → TorusHk (s k) ℂ),
        (∀ i, CellWeakHilbertCurve a t (Ψv i) (Ψs i) (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs i r) 0 0)) ∧
        (∀ i, Ψv i t = torusHkValueCLM (ψ i)) ∧
        (∀ i, ∀ r ∈ Icc a t, torusHkValueCLM (U i r) = Ψv i r) ∧
        ∀ r ∈ Icc a t, Real.sqrt (∑ i ∈ stageSet st k, ‖U i r‖ ^ 2) ≤
          Ca * κ r t * Real.sqrt (∑ i ∈ stageSet st k, ‖ψ i‖ ^ 2))
    (hrep : ∀ k < M, ∀ᵐ r ∂volume.restrict (Icc a b), ∀ (z : I → TorusHk 1 ℂ)
      (ψ : I → TorusHk (s k) ℂ), (∀ i, torusHkValueCLM (z i) = torusHkValueCLM (ψ i)) →
      ∃ Φ : ∀ k', I → TorusHk (s k') ℂ,
        (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ‖Φ k' i'‖ ^ 2) ≤
          B * Real.sqrt (∑ i ∈ stageSet st k, ‖ψ i‖ ^ 2)) ∧
        ∑ i ∈ stageSet st k, cellComplexSource C.θ (S i r) (Fl i r) (z i) =
          ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
            cellComplexPair (W i' r) (torusHkValueCLM (Φ k' i'))) :
    ∀ k < M, ∀ t ∈ Icc a b, ∀ ψ : I → TorusHk (s k) ℂ,
      ‖∑ i ∈ stageSet st k, cellComplexPair (W i t) (torusHkValueCLM (ψ i))‖ ≤
        plainConst Ca A B k * (1 + (t - a)) ^ k * κ a t *
          Real.sqrt (∑ i, ‖W i a‖ ^ 2) * Real.sqrt (∑ i ∈ stageSet st k, ‖ψ i‖ ^ 2) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk t ht ψ
  set X := Real.sqrt (∑ i, ‖W i a‖ ^ 2) with hXdef
  set Y := Real.sqrt (∑ i ∈ stageSet st k, ‖ψ i‖ ^ 2) with hYdef
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  obtain ⟨Ψv, Ψs, U, hΨ, hΨt, hU, hUn⟩ := hadj k hk t ht ψ
  have hat : a ≤ t := ht.1
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  -- the duality, member by member
  have hF1 : ∀ i, cellComplexPair (W i t) (torusHkValueCLM (ψ i)) =
      cellComplexPair (W i a) (Ψv i a) +
        ∫ r in a..t, cellComplexSource C.θ (S i r) (Fl i r) (Ψs i r) := by
    intro i
    have h := cellWeakAdjointPairing_forced hat C hG V hv hb ((hW i).mono hsub) (hΨ i)
    rw [hΨt i] at h
    rw [← h]
    ring
  have hint : ∀ i, IntervalIntegrable
      (fun r => cellComplexSource C.θ (S i r) (Fl i r) (Ψs i r)) volume a t := fun i =>
    cellWeakAdjoint_forced_source_intervalIntegrable hat C hG V hv hb ((hW i).mono hsub) (hΨ i)
  have hsum : ∑ i ∈ stageSet st k, cellComplexPair (W i t) (torusHkValueCLM (ψ i)) =
      ∑ i ∈ stageSet st k, cellComplexPair (W i a) (Ψv i a) +
        ∫ r in a..t, ∑ i ∈ stageSet st k, cellComplexSource C.θ (S i r) (Fl i r) (Ψs i r) := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => hint i), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hF1 i
  -- the initial term
  have haI : a ∈ Icc a t := ⟨le_rfl, hat⟩
  have hinit : ‖∑ i ∈ stageSet st k, cellComplexPair (W i a) (Ψv i a)‖ ≤
      Ca * κ a t * X * Y := by
    refine (pair_sum_le (stageSet st k) Finset.univ (Finset.subset_univ _) (fun i => W i a)
      (fun i => U i a) (fun i => Ψv i a) fun i _ => (hU i a haI).symm).trans ?_
    calc X * Real.sqrt (∑ i ∈ stageSet st k, ‖U i a‖ ^ 2) ≤ X * (Ca * κ a t * Y) :=
          mul_le_mul_of_nonneg_left (hUn a haI) hX0
      _ = Ca * κ a t * X * Y := by ring
  -- the integral term
  set Sk := ∑ k' ∈ Finset.range k, plainConst Ca A B k' with hSk
  have hSk0 : 0 ≤ Sk := Finset.sum_nonneg fun k' _ => plainConst_nonneg hCa hA hB k'
  have hpt : ∀ᵐ r ∂volume, r ∈ Ioc a t →
      ‖∑ i ∈ stageSet st k, cellComplexSource C.θ (S i r) (Fl i r) (Ψs i r)‖ ≤
        A * B * Ca * Sk * (1 + (t - a)) ^ (k - 1) * κ a t * X * Y := by
    have h1 := (ae_restrict_iff' measurableSet_Icc).1 (hrep k hk)
    have h2 : ∀ᵐ r ∂volume, r ∈ Icc a t → ∀ i, Ψv i r = torusHkValueCLM (Ψs i r) := by
      rw [← ae_restrict_iff' measurableSet_Icc]
      exact ae_all_iff.2 fun i => (hΨ i).agrees
    filter_upwards [h1, h2] with r hr1 hr2 hr
    have hrI : r ∈ Icc a t := ⟨hr.1.le, hr.2⟩
    obtain ⟨Φ, hΦn, hΦe⟩ := hr1 (hsub hrI) (fun i => Ψs i r) (fun i => U i r)
      (fun i => by rw [← hr2 hrI i, hU i r hrI])
    rw [hΦe]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k' ∈ Finset.range k, ‖∑ i' ∈ stageSet st k',
          cellComplexPair (W i' r) (torusHkValueCLM (Φ k' i'))‖
        ≤ ∑ k' ∈ Finset.range k, A * B * Ca * plainConst Ca A B k' * (1 + (t - a)) ^ (k - 1) *
            κ a t * X * Y := by
          refine Finset.sum_le_sum fun k' hk' => ?_
          have hk'k := Finset.mem_range.1 hk'
          refine (ih k' hk'k (hk'k.trans hk) r (hsub hrI) (Φ k')).trans ?_
          have hb1 := (hΦn k' hk'k).trans
            (mul_le_mul_of_nonneg_left (hUn r hrI) hB)
          calc plainConst Ca A B k' * (1 + (r - a)) ^ k' * κ a r * X *
                Real.sqrt (∑ i' ∈ stageSet st k', ‖Φ k' i'‖ ^ 2)
              ≤ plainConst Ca A B k' * (1 + (r - a)) ^ k' * κ a r * X *
                  (B * (Ca * κ r t * Y)) :=
                mul_le_mul_of_nonneg_left hb1
                  (mul_nonneg (mul_nonneg (mul_nonneg (plainConst_nonneg hCa hA hB k')
                    (pow_nonneg (by linarith [hr.1]) _)) (hκ a r)) hX0)
            _ ≤ A * B * Ca * plainConst Ca A B k' * (1 + (t - a)) ^ (k - 1) * κ a t * X * Y :=
                plain_term_le hk'k (plainConst_nonneg hCa hA hB k') hB hCa hX0 hY0 (hκ a r)
                  (hκ r t) (hmul r t hrI.1 hrI.2 ht.2) (by linarith [hr.1]) (by linarith [hr.2])
      _ = A * B * Ca * Sk * (1 + (t - a)) ^ (k - 1) * κ a t * X * Y := by
          rw [hSk]
          simp only [Finset.mul_sum, Finset.sum_mul]
  have hIint : ‖∫ r in a..t, ∑ i ∈ stageSet st k,
      cellComplexSource C.θ (S i r) (Fl i r) (Ψs i r)‖ ≤
      (t - a) * (A * B * Ca * Sk * (1 + (t - a)) ^ (k - 1) * κ a t * X * Y) := by
    refine (intervalIntegral.norm_integral_le_of_norm_le hat hpt intervalIntegrable_const).trans ?_
    rw [intervalIntegral.integral_const, smul_eq_mul]
  rw [hsum, plainConst_eq]
  exact (norm_add_le _ _).trans (plain_step_le (k := k) (fun hk0 => by subst hk0; simp)
    (by linarith) hCa (hκ a t) hX0 hY0 hSk0 hinit hIint (by positivity))

end Pass
end

/-! # the stages on nested terminal windows, abstract form

Stage curves `W_i` on `[T, b]`, stage orders `st i`, positive orders `n_i`. The stage of order `k`
lives on the window `[T + kτ, b]`: its value at `T + kτ` is bounded against tests (`M`, negative
order); its forcing is represented in `H^{n_i}` by the earlier stages (`hsrc`, the source bound),
which are already positive on that window; one window step (`hwin`) makes it positive from
`T + (k+1)τ` on. So every stage `i` is in `H^{n_i}` on `[T + (st i + 1)τ, b]`, with the constants
`termConst Λ T_τ B c`, where `termConst k = Λ(T_τ + B√c ∑_{k'<k} termConst k')`. -/

section
open AVRegularity.CycleWords.Assembly

/-- The constants of the terminal pass. -/
def termConst (Λ Tτ B c : ℝ) : ℕ → ℝ
  | k => Λ * (Tτ + B * Real.sqrt c * ∑ k' : Fin k, termConst Λ Tτ B c k')
termination_by k => k
decreasing_by exact k'.isLt

theorem termConst_eq (Λ Tτ B c : ℝ) (k : ℕ) :
    termConst Λ Tτ B c k =
      Λ * (Tτ + B * Real.sqrt c * ∑ k' ∈ Finset.range k, termConst Λ Tτ B c k') := by
  rw [termConst, Finset.sum_range]

theorem termConst_nonneg {Λ Tτ B c : ℝ} (hΛ : 0 ≤ Λ) (hT : 0 ≤ Tτ) (hB : 0 ≤ B) (k : ℕ) :
    0 ≤ termConst Λ Tτ B c k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [termConst_eq]
    have : 0 ≤ ∑ k' ∈ Finset.range k, termConst Λ Tτ B c k' :=
      Finset.sum_nonneg fun k' hk' => ih k' (Finset.mem_range.1 hk')
    positivity
end

/-! # the stage families on nested terminal windows

`terminal_pass_family`: the terminal pass, with the stages of one order treated as a family and
every bound in `ℓ²` over the family: the negative-order input, the forcing (the source bound) and the window
step (`hwin`, from `window_family_hs`). The constants are those of `termConst Λ T_τ B 1`,
independent of the number of stages. -/

section
open AVRegularity.CycleWords.Assembly

section Pass

variable {I : Type*} [Fintype I]

/-- `∑ x_k² ≤ (∑ x_k)²` for nonnegative terms. -/
theorem fullField_sum_sq_le_sq_sum (k : ℕ) (x : ℕ → ℝ) (hx : ∀ k', 0 ≤ x k') :
    ∑ k' ∈ Finset.range k, x k' ^ 2 ≤ (∑ k' ∈ Finset.range k, x k') ^ 2 := by
  rw [sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun k' hk' => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => hx j) hk') (hx k')

/-- **The terminal pass on stage families, abstract form.** -/
theorem terminal_pass_family (st : I → ℕ) (Mst : ℕ) (n : I → ℕ) (s : ℕ → ℕ) {T b τ : ℝ}
    (hτ : 0 < τ) (θc : Fin 2 → ℂ) (W : I → ℝ → ComplexCellL2) (S : I → ℝ → ComplexCellL2)
    (Fl : I → ℝ → Fin 2 → ComplexCellL2) (Λ Tτ B M : ℝ) (hΛ : 0 ≤ Λ) (hT : 0 ≤ Tτ)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hwin : ∀ k < Mst, ∀ t₀ ∈ Icc T b, ∀ M' : ℝ, 0 ≤ M' →
      (∀ ψ : I → TorusHk (s k) ℂ, ‖∑ i ∈ stageSet st k,
          cellComplexPair (W i t₀) (torusHkValueCLM (ψ i))‖ ≤
        M' * Real.sqrt (∑ i ∈ stageSet st k, ‖ψ i‖ ^ 2)) →
      ∀ (σ : ℝ → ∀ i, TorusHk (n i) ℂ) (f : ℝ → ℝ), IntegrableOn f (Icc t₀ b) →
        (∀ᵐ t ∂volume.restrict (Icc t₀ b),
          Real.sqrt (∑ i ∈ stageSet st k, ‖σ t i‖ ^ 2) ≤ f t ∧
          ∀ i ∈ stageSet st k, ∀ z : TorusHk 1 ℂ,
            cellComplexSource θc (S i t) (Fl i t) z =
              cellComplexPair (torusHkValueCLM (σ t i)) (torusHkValueCLM z)) →
      ∀ t ∈ Icc t₀ b, t₀ + τ ≤ t →
        ∃ X : ∀ i, TorusHk (n i) ℂ, (∀ i ∈ stageSet st k, torusHkValueCLM (X i) = W i t) ∧
          Real.sqrt (∑ i ∈ stageSet st k, ‖X i‖ ^ 2) ≤ Λ * (Tτ * M' + ∫ r in t₀..t, f r))
    (hlen : ∀ t₀ ∈ Icc T b, ∀ t ∈ Icc t₀ b, t - t₀ ≤ 1)
    (hstep : ∀ k < Mst, T + (k : ℝ) * τ ∈ Icc T b)
    (hneg : ∀ k < Mst, ∀ ψ : I → TorusHk (s k) ℂ,
      ‖∑ i ∈ stageSet st k,
          cellComplexPair (W i (T + (k : ℝ) * τ)) (torusHkValueCLM (ψ i))‖ ≤
        M * Real.sqrt (∑ i ∈ stageSet st k, ‖ψ i‖ ^ 2))
    (hsrc : ∀ᵐ r ∂volume.restrict (Icc T b), ∀ (k : ℕ) (X : ∀ i, TorusHk (n i) ℂ),
      (∀ i', st i' < k → torusHkValueCLM (X i') = W i' r) →
      ∃ σ : ∀ i, TorusHk (n i) ℂ,
        (∀ i ∈ stageSet st k, ∀ z : TorusHk 1 ℂ, cellComplexSource θc (S i r) (Fl i r) z =
          cellComplexPair (torusHkValueCLM (σ i)) (torusHkValueCLM z)) ∧
        ∑ i ∈ stageSet st k, ‖σ i‖ ^ 2 ≤
          B ^ 2 * ∑ i' ∈ Finset.univ.filter (fun i' => st i' < k), ‖X i'‖ ^ 2) :
    ∀ k < Mst, ∀ t ∈ Icc (T + ((k : ℝ) + 1) * τ) b,
      ∃ X : ∀ i, TorusHk (n i) ℂ, (∀ i ∈ stageSet st k, torusHkValueCLM (X i) = W i t) ∧
        Real.sqrt (∑ i ∈ stageSet st k, ‖X i‖ ^ 2) ≤ termConst Λ Tτ B 1 k * M := by
  classical
  set Φ := termConst Λ Tτ B 1 with hΦdef
  have hΦ0 : ∀ k', 0 ≤ Φ k' := termConst_nonneg hΛ hT hB
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk t ht
  -- the earlier families, on the window of the order `k`
  have hE : ∀ (k' : ℕ) (r : ℝ), ∃ X : ∀ i, TorusHk (n i) ℂ, k' < k →
      r ∈ Icc (T + (k : ℝ) * τ) b →
      (∀ i ∈ stageSet st k', torusHkValueCLM (X i) = W i r) ∧
      Real.sqrt (∑ i ∈ stageSet st k', ‖X i‖ ^ 2) ≤ Φ k' * M := by
    intro k' r
    by_cases h : k' < k ∧ r ∈ Icc (T + (k : ℝ) * τ) b
    · have hle : T + ((k' : ℝ) + 1) * τ ≤ T + (k : ℝ) * τ := by
        have : ((k' : ℝ) + 1) ≤ k := by exact_mod_cast h.1
        nlinarith
      obtain ⟨X, hX, hXn⟩ := ih k' h.1 (h.1.trans hk) r ⟨hle.trans h.2.1, h.2.2⟩
      exact ⟨X, fun _ _ => ⟨hX, hXn⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Xe hXe using hE
  -- the forcing of the order `k`
  set fc := B * ((∑ k' ∈ Finset.range k, Φ k') * M) with hfc
  have hS0 : 0 ≤ ∑ k' ∈ Finset.range k, Φ k' := Finset.sum_nonneg fun k' _ => hΦ0 k'
  have hfc0 : 0 ≤ fc := by positivity
  have hY : ∀ r ∈ Icc (T + (k : ℝ) * τ) b,
      ∑ i' ∈ Finset.univ.filter (fun i' => st i' < k), ‖Xe (st i') r i'‖ ^ 2 ≤
        ((∑ k' ∈ Finset.range k, Φ k') * M) ^ 2 := by
    intro r hr
    have hfib : ∑ i' ∈ Finset.univ.filter (fun i' => st i' < k), ‖Xe (st i') r i'‖ ^ 2 =
        ∑ k' ∈ Finset.range k, ∑ i ∈ stageSet st k', ‖Xe k' r i‖ ^ 2 := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun i' => st i' < k))
        (t := Finset.range k) (g := st) (fun i hi => Finset.mem_range.2 (Finset.mem_filter.1 hi).2)]
      refine Finset.sum_congr rfl fun k' hk' => ?_
      unfold stageSet
      rw [Finset.filter_filter]
      refine Finset.sum_congr ?_ fun i hi => ?_
      · ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, h⟩
          exact h
        · intro h
          exact ⟨h ▸ Finset.mem_range.1 hk', h⟩
      · rw [(Finset.mem_filter.1 hi).2]
    rw [hfib]
    calc ∑ k' ∈ Finset.range k, ∑ i ∈ stageSet st k', ‖Xe k' r i‖ ^ 2
        ≤ ∑ k' ∈ Finset.range k, (Φ k' * M) ^ 2 := by
          refine Finset.sum_le_sum fun k' hk' => ?_
          have h := (hXe k' r (Finset.mem_range.1 hk') hr).2
          have h0 : 0 ≤ ∑ i ∈ stageSet st k', ‖Xe k' r i‖ ^ 2 :=
            Finset.sum_nonneg fun i _ => sq_nonneg _
          calc ∑ i ∈ stageSet st k', ‖Xe k' r i‖ ^ 2
              = Real.sqrt (∑ i ∈ stageSet st k', ‖Xe k' r i‖ ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
            _ ≤ (Φ k' * M) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      _ ≤ (∑ k' ∈ Finset.range k, Φ k' * M) ^ 2 :=
          fullField_sum_sq_le_sq_sum k (fun k' => Φ k' * M) fun k' => mul_nonneg (hΦ0 k') hM
      _ = ((∑ k' ∈ Finset.range k, Φ k') * M) ^ 2 := by rw [Finset.sum_mul]
  have hσ : ∀ r : ℝ, ∃ σ : ∀ i, TorusHk (n i) ℂ,
      r ∈ Icc (T + (k : ℝ) * τ) b →
      (∀ (k' : ℕ) (X : ∀ i, TorusHk (n i) ℂ), (∀ i', st i' < k' → torusHkValueCLM (X i') = W i' r) →
        ∃ σ : ∀ i, TorusHk (n i) ℂ,
          (∀ i ∈ stageSet st k', ∀ z : TorusHk 1 ℂ, cellComplexSource θc (S i r) (Fl i r) z =
            cellComplexPair (torusHkValueCLM (σ i)) (torusHkValueCLM z)) ∧
          ∑ i ∈ stageSet st k', ‖σ i‖ ^ 2 ≤
            B ^ 2 * ∑ i' ∈ Finset.univ.filter (fun i' => st i' < k'), ‖X i'‖ ^ 2) →
      (∀ i ∈ stageSet st k, ∀ z : TorusHk 1 ℂ, cellComplexSource θc (S i r) (Fl i r) z =
        cellComplexPair (torusHkValueCLM (σ i)) (torusHkValueCLM z)) ∧
      ∑ i ∈ stageSet st k, ‖σ i‖ ^ 2 ≤
        B ^ 2 * ∑ i' ∈ Finset.univ.filter (fun i' => st i' < k), ‖Xe (st i') r i'‖ ^ 2 := by
    intro r
    by_cases hr : r ∈ Icc (T + (k : ℝ) * τ) b
    · by_cases hP : ∀ (k' : ℕ) (X : ∀ i, TorusHk (n i) ℂ),
          (∀ i', st i' < k' → torusHkValueCLM (X i') = W i' r) →
          ∃ σ : ∀ i, TorusHk (n i) ℂ,
            (∀ i ∈ stageSet st k', ∀ z : TorusHk 1 ℂ, cellComplexSource θc (S i r) (Fl i r) z =
              cellComplexPair (torusHkValueCLM (σ i)) (torusHkValueCLM z)) ∧
            ∑ i ∈ stageSet st k', ‖σ i‖ ^ 2 ≤
              B ^ 2 * ∑ i' ∈ Finset.univ.filter (fun i' => st i' < k'), ‖X i'‖ ^ 2
      · obtain ⟨σ, hσ1, hσ2⟩ := hP k (fun i' => Xe (st i') r i') fun i' hi' =>
          (hXe (st i') r hi' hr).1 i' (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
        exact ⟨σ, fun _ _ => ⟨hσ1, hσ2⟩⟩
      · exact ⟨0, fun _ h => absurd h hP⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose σ hσp using hσ
  have hstep_k := hstep k hk
  have hsub : Icc (T + (k : ℝ) * τ) b ⊆ Icc T b := Icc_subset_Icc hstep_k.1 le_rfl
  have hae : ∀ᵐ r ∂volume.restrict (Icc (T + (k : ℝ) * τ) b),
      Real.sqrt (∑ i ∈ stageSet st k, ‖σ r i‖ ^ 2) ≤ fc ∧
      ∀ i ∈ stageSet st k, ∀ z : TorusHk 1 ℂ, cellComplexSource θc (S i r) (Fl i r) z =
        cellComplexPair (torusHkValueCLM (σ r i)) (torusHkValueCLM z) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hsrc,
      ae_restrict_mem measurableSet_Icc] with r hP hr
    obtain ⟨h1, h2⟩ := hσp r hr hP
    refine ⟨?_, h1⟩
    have hsq : ∑ i ∈ stageSet st k, ‖σ r i‖ ^ 2 ≤ fc ^ 2 := by
      calc ∑ i ∈ stageSet st k, ‖σ r i‖ ^ 2
          ≤ B ^ 2 * ((∑ k' ∈ Finset.range k, Φ k') * M) ^ 2 :=
            h2.trans (mul_le_mul_of_nonneg_left (hY r hr) (sq_nonneg B))
        _ = fc ^ 2 := by rw [hfc]; ring
    calc Real.sqrt (∑ i ∈ stageSet st k, ‖σ r i‖ ^ 2) ≤ Real.sqrt (fc ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = fc := Real.sqrt_sq hfc0
  -- one window step
  have ht' : t ∈ Icc (T + (k : ℝ) * τ) b := ⟨by nlinarith [ht.1], ht.2⟩
  obtain ⟨X, hX, hXn⟩ := hwin k hk (T + (k : ℝ) * τ) hstep_k M hM (hneg k hk) σ (fun _ => fc)
    (integrableOn_const measure_Icc_lt_top.ne) hae t ht' (by nlinarith [ht.1])
  refine ⟨X, hX, hXn.trans ?_⟩
  have hint : ∫ r in (T + (k : ℝ) * τ)..t, fc ≤ fc := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    have h1 := hlen (T + (k : ℝ) * τ) hstep_k t ht'
    have h0 : 0 ≤ t - (T + (k : ℝ) * τ) := by linarith [ht'.1]
    nlinarith
  rw [hΦdef, termConst_eq, ← hΦdef, Real.sqrt_one, mul_one]
  calc Λ * (Tτ * M + ∫ r in (T + (k : ℝ) * τ)..t, fc) ≤ Λ * (Tτ * M + fc) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hint) hΛ
    _ = Λ * (Tτ + B * ∑ k' ∈ Finset.range k, Φ k') * M := by
        rw [hfc]
        ring

end Pass
end

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # the representation of the tested sources with the plain families

`b1w_repr_crude_at`: at a good time, the tested sources of the stages of order `k` against
`H^N` tests are the earlier stages paired with the transform families of the tests. This is
`b1w_sharp_repr_general_at` with the plain families (the value identity and the `ℓ²` bound, as
`StageFamilyZoneStatement` gives them) in place of the sharp ones, and tests of order
`n + 2 ≤ N` (their classical representatives are `C^n`). -/

universe u v

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The tested sources at a good time, with the plain families.** -/
theorem b1w_repr_crude_at {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (k : ℕ) (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (s : ℕ → ℕ) (n N : ℕ) (hn1 : 1 ≤ n)
    (hN : n + 2 ≤ N)
    (W S : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (Fl : B1WIndex ι h Nw m Ks → Fin 2 → ComplexCellL2)
    (hS : ∀ i ∈ stageSet b1wSt k, (S i : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y)
    (hF : ∀ i ∈ stageSet b1wSt k, ∀ j, (Fl i j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y j)
    (hExp : ∀ i ∈ stageSet b1wSt k, ∀ φ : Vec 2 → ℂ, ContDiff ℝ n φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ i ∈ stageSet b1wSt k, ∀ i' : B1WIndex ι h Nw m Ks, ¬ b1wSt i' < k →
      ∀ φ : Vec 2 → ℂ,
      b1wTestTransform F θ i i' r φ = 0)
    (hW : ∀ i' : B1WIndex ι h Nw m Ks, (W i' : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i' * b1wStageVal F θ i' r y)
    (B : ℝ)
    (hprov : ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ, ∀ k' < k,
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
        (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
          =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
            ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
              star (b1wTestTransform F θ i i' r (fun y => star
                (torusHigherClassicalValue N (ψ i) y)) y)) ∧
        ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)
    (z : B1WIndex ι h Nw m Ks → TorusHk 1 ℂ) (ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ)
    (hzψ : ∀ i, torusHkValueCLM (z i) = torusHkValueCLM (ψ i)) :
    ∃ (UΦ : ∀ k', B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ)
      (Φall : B1WIndex ι h Nw m Ks → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet b1wSt k', torusHkValueCLM (UΦ k' i') = Φall i') ∧
      (∀ k' < k, ∑ i' ∈ stageSet b1wSt k', ‖UΦ k' i'‖ ^ 2 ≤
        B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) ∧
      ∑ i ∈ stageSet b1wSt k, cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) (z i) =
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k', cellComplexPair (W i') (Φall i') := by
  classical
  -- the families of the tests
  choose Φf hΦf using hprov ψ
  obtain ⟨UΦ, hUΦdef⟩ : ∃ UΦ : ∀ k', B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
      UΦ = fun k' => if hk : k' < k then Φf k' hk else fun _ => 0 := ⟨_, rfl⟩
  have hUΦk : ∀ k' (hk : k' < k), UΦ k' = Φf k' hk := fun k' hk => by
    rw [hUΦdef]
    simp only [hk, dite_true]
  obtain ⟨Φall, hΦall⟩ : ∃ Φall : B1WIndex ι h Nw m Ks → ComplexCellL2,
      Φall = fun i' => torusHkValueCLM (UΦ (b1wSt i') i') := ⟨_, rfl⟩
  have hUΦval : ∀ k' < k, ∀ i' ∈ stageSet b1wSt k', torusHkValueCLM (UΦ k' i') = Φall i' := by
    intro k' _ i' hi'
    have hst : b1wSt i' = k' := (Finset.mem_filter.1 hi').2
    rw [hΦall]
    subst hst
    rfl
  -- the classical representatives of the tests
  have hcl : ∀ i, ContDiff ℝ (n : ℕ) (torusHigherClassicalValue N (ψ i)) := fun i =>
    torusHigherClassicalValue_contDiff N n hN (ψ i)
  have hzcl : ∀ i, (torusHkValueCLM (z i) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      torusHigherClassicalValue N (ψ i) := by
    intro i
    rw [hzψ i]
    exact (torusHigherClassicalValue_ae N (by omega) (ψ i)).symm
  have hstc : ∀ i, ContDiff ℝ n (fun y => star (torusHigherClassicalValue N (ψ i) y)) :=
    fun i => Complex.conjCLE.toContinuousLinearMap.contDiff.comp
      ((hcl i).of_le (by exact_mod_cast le_rfl))
  have hper : ∀ i, AVenhance.IsZ2Periodic (fun y => star (torusHigherClassicalValue N (ψ i) y)) :=
    fun i mm y => by simp only [torusHigherClassicalValue_periodic N (ψ i) mm y]
  have hc1 : ∀ i, ContDiff ℝ 1 (torusHigherClassicalValue N (ψ i)) := fun i =>
    (hcl i).of_le (by exact_mod_cast hn1)
  have hint : ∀ i ∈ stageSet b1wSt k, ∀ i', b1wSt i' < k →
      Integrable (fun y => b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' * (W i' y *
        b1wTestTransform F θ i i' r (fun y => star (torusHigherClassicalValue N (ψ i) y)) y))
        (volume.restrict AVenhance.unitCube) := by
    intro i hi i' hi'
    obtain ⟨Φ1, hΦ1⟩ := hprov (fun j => if j = i then ψ i else 0) (b1wSt i') hi'
    have hv := hΦ1.1 i' (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)
    refine (cellComplex_pairing_integrable (W i') (torusHkValueCLM (Φ1 i'))).congr ?_
    filter_upwards [hv] with y hy
    rw [hy, Finset.sum_eq_single_of_mem i hi fun j _ hj => ?_]
    · simp only [ite_true, star_mul', star_star, b1wScaleRatio_star]
      ring
    · simp only [hj, ite_false, torusHigherClassicalValue_zero N (by omega), Pi.zero_apply,
        star_zero, b1wTestTransform_zero_test, mul_zero]
  have hrep := b1w_stage_representation F θ r k hπ hϖ W S Fl z
    (fun i => torusHigherClassicalValue N (ψ i)) (fun i _ => hc1 i)
    (fun i _ => hzcl i) hS hF (fun i hi => hExp i hi _ (hstc i) (hper i))
    (fun i hi i' hi' => hearly i hi i' hi' _) hW hint Φall
    (fun i' hi' => by
      rw [hΦall]
      simp only []
      rw [hUΦk _ hi']
      exact (hΦf (b1wSt i') hi').1 i' (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩))
  refine ⟨UΦ, Φall, hUΦval, fun k' hk' => ?_, hrep⟩
  rw [hUΦk k' hk']
  exact (hΦf k' hk').2

end Frame

end AVRegularity.CycleWords.Assembly
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleWords.Assembly
open scoped Topology
namespace AVRegularity.CycleWords.Discard

/-! # integration by parts for `H^{K+1}` against smooth periodic tests

For `X ∈ H^{K+1}` of the torus and a `C¹` periodic test `φ`,
`∫ X · D_{-θ,k} φ = -∫ (tbTwist K θ k X) · φ`
(`torusHk_integration_by_parts`), with `D_{-θ,k} = fibreCovDeriv (-θ) k`. `X` has no classical representative when `K`
is small: the identity is proved for the Fourier truncations `galerkinProj N X` (smooth
representatives; `integral_mul_fibreCovDeriv_neg`) and passed to the limit, both sides being
continuous in `X`. -/

/-- The cell pairing with a continuous test is continuous on `L²` of the cell. -/
theorem pair_continuous (ψ : Vec 2 → ℂ) (hψ : Continuous ψ) :
    Continuous (fun u : ComponentL2 (volume.restrict AVenhance.unitCube) ℂ =>
      ∫ y in AVenhance.unitCube, (u : Vec 2 → ℂ) y * ψ y) := by
  have hm : MemLp (fun y => star (ψ y)) 2 (volume.restrict AVenhance.unitCube) :=
    AVRegularity.CycleComparison.Lift.continuous_cell_memLp _ (continuous_star.comp hψ)
  let g := hm.toLp (fun y => star (ψ y))
  have hc : Continuous (fun u : ComponentL2 (volume.restrict AVenhance.unitCube) ℂ =>
      inner ℂ g u) := (innerSL ℂ g).continuous
  refine hc.congr fun u => ?_
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hm.coeFn_toLp] with y hy
  rw [hy]
  simp [mul_comm]

/-- The smooth representative of a Fourier truncation. -/
theorem galerkin_smooth (K : ℕ) (N : ℕ) (X : TorusHk (K + 1) ℂ) :
    ContDiff ℝ 1 (smoothFourierJet (K := K + 1) (L := K + 1) N X (valueIndex2 (K + 1))) ∧
    AVenhance.IsZ2Periodic (smoothFourierJet (K := K + 1) (L := K + 1) N X (valueIndex2 (K + 1))) ∧
    (torusHkValueCLM (galerkinProj (E := ℂ) (K := K + 1) N X) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube]
      smoothFourierJet (K := K + 1) (L := K + 1) N X (valueIndex2 (K + 1)) := by
  refine ⟨(smoothFourierJet_contDiff N X _).of_le (by simp),
    smoothFourierJet_periodic N X _, ?_⟩
  have h := torusJetToL2_ae (smoothFourierJet (K := K + 1) (L := K + 1) N X)
    (smoothFourierJet_memLp (K := K + 1) (L := K + 1) N X) (valueIndex2 (K + 1))
  change (torusHkValueCLM (smoothFourierLift (K := K + 1) (L := K + 1) N X) : Vec 2 → ℂ)
    =ᵐ[volume.restrict AVenhance.unitCube]
      smoothFourierJet (K := K + 1) (L := K + 1) N X (valueIndex2 (K + 1)) at h
  rw [smoothFourierLift_value_projection] at h
  exact h

/-- **Integration by parts for `H^{K+1}` against a smooth periodic test.** -/
theorem torusHk_integration_by_parts (K : ℕ) (θ : Vec 2) (k : Fin 2) (X : TorusHk (K + 1) ℂ) (φ : Vec 2 → ℂ)
    (hφ : ContDiff ℝ 1 φ) (hφp : AVenhance.IsZ2Periodic φ) :
    ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y * fibreCovDeriv (-θ) k φ y =
      -∫ y in AVenhance.unitCube,
        (torusHkValueCLM (tbTwist K θ k X) : Vec 2 → ℂ) y * φ y := by
  have hψ : Continuous (fibreCovDeriv (-θ) k φ) :=
    (contDiff_fibreCovDeriv (j := 0) (by simpa using hφ) _ k).continuous
  have hL : Continuous (fun Y : TorusHk (K + 1) ℂ =>
      ∫ y in AVenhance.unitCube, (torusHkValueCLM Y : Vec 2 → ℂ) y * fibreCovDeriv (-θ) k φ y) :=
    (pair_continuous _ hψ).comp (torusHkValueCLM (E := ℂ) (K := K + 1)).continuous
  have hR : Continuous (fun Y : TorusHk (K + 1) ℂ =>
      -∫ y in AVenhance.unitCube, (torusHkValueCLM (tbTwist K θ k Y) : Vec 2 → ℂ) y * φ y) :=
    ((pair_continuous _ hφ.continuous).comp
      ((torusHkValueCLM (E := ℂ) (K := K)).continuous.comp
        (tbTwist K θ k).continuous)).neg
  have hT := galerkinProj_tendsto (E := ℂ) (K := K + 1) X
  refine tendsto_nhds_unique ((hL.tendsto X).comp hT) ?_
  have hR' := (hR.tendsto X).comp hT
  refine hR'.congr fun N => ?_
  obtain ⟨hc, hp, hae⟩ := galerkin_smooth K N X
  set f := smoothFourierJet (K := K + 1) (L := K + 1) N X (valueIndex2 (K + 1))
  have htw := tbTwist_value_ae K θ k _ f hc hae
  have e1 : ∫ y in AVenhance.unitCube,
      (torusHkValueCLM (galerkinProj (E := ℂ) (K := K + 1) N X) : Vec 2 → ℂ) y *
        fibreCovDeriv (-θ) k φ y = ∫ y in AVenhance.unitCube, f y * fibreCovDeriv (-θ) k φ y :=
    integral_congr_ae (by filter_upwards [hae] with y hy; rw [hy])
  have e2 : ∫ y in AVenhance.unitCube,
      (torusHkValueCLM (tbTwist K θ k (galerkinProj (E := ℂ) (K := K + 1) N X)) :
        Vec 2 → ℂ) y * φ y = ∫ y in AVenhance.unitCube, fibreCovDeriv θ k f y * φ y :=
    integral_congr_ae (by filter_upwards [htw] with y hy; rw [hy])
  simp only [Function.comp_apply]
  rw [e1, e2]
  exact (integral_mul_fibreCovDeriv_neg θ k hc hφ hp hφp).symm

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleWords.Assembly
namespace AVRegularity.CycleWords.Discard

/-! # iterated integration by parts

`fwdPow θ n q p : H^{n+q+p} → H^n` is `(∂_1 + iθ_1)^q (∂_0 + iθ_0)^p`, the transpose of
`fibreCovPow (-θ) (p, q) = D_{-θ,0}^p D_{-θ,1}^q`:
`∫ X · D_{-θ,0}^p D_{-θ,1}^q f = (-1)^{p+q} ∫ (fwdPow X) · f` (`ibp_pow`), obtained by
iterating `torusHk_integration_by_parts` (`ibp_iter`). -/

/-- `m` integrations by parts in one direction. -/
theorem ibp_iter (θ : Vec 2) (k : Fin 2) (K : ℕ) :
    ∀ (m : ℕ) (X : TorusHk (K + m) ℂ) (φ : Vec 2 → ℂ), ContDiff ℝ (m : ℕ) φ →
      AVenhance.IsZ2Periodic φ →
      ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y *
          (fibreCovDeriv (-θ) k)^[m] φ y =
        (-1 : ℂ) ^ m * ∫ y in AVenhance.unitCube,
          (torusHkValueCLM (twIter θ k K m X) : Vec 2 → ℂ) y * φ y
  | 0, X, φ, _, _ => by simp [twIter]
  | m + 1, X, φ, hφ, hp => by
    have hg : ContDiff ℝ 1 ((fibreCovDeriv (-θ) k)^[m] φ) :=
      contDiff_fibreCovDeriv_iterate (-θ) k 1 m (by simpa [add_comm] using hφ)
    have hgp : AVenhance.IsZ2Periodic ((fibreCovDeriv (-θ) k)^[m] φ) :=
      isZ2Periodic_fibreCovDeriv_iterate (-θ) k m hp
    have h1 := torusHk_integration_by_parts (K + m) θ k X _ hg hgp
    have h2 := ibp_iter θ k K m (tbTwist (K + m) θ k X) φ
      (hφ.of_le (by exact_mod_cast Nat.le_succ m)) hp
    rw [Function.iterate_succ_apply', h1, h2]
    change _ = (-1 : ℂ) ^ (m + 1) * ∫ y in AVenhance.unitCube,
      (torusHkValueCLM (twIter θ k K m (tbTwist (K + m) θ k X)) : Vec 2 → ℂ) y * φ y
    rw [pow_succ]
    ring

/-- The transposed twisted power `(∂_1 + iθ_1)^q (∂_0 + iθ_0)^p : H^{n+q+p} → H^n`. -/
def fwdPow (θ : Vec 2) (n q p : ℕ) : TorusHk (n + q + p) ℂ →L[ℝ] TorusHk n ℂ :=
  (twIter θ 1 n q).comp (twIter θ 0 (n + q) p)

theorem fwdPow_norm (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n q p : ℕ)
    (U : TorusHk (n + q + p) ℂ) : ‖fwdPow θ n q p U‖ ≤ (1 + ρ) ^ (p + q) * ‖U‖ := by
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
  have h1 := twIter_norm θ 0 (n + q) p U
  have h2 := twIter_norm θ 1 n q (twIter θ 0 (n + q) p U)
  have a1 : (1 + |θ 1|) ^ q ≤ (1 + ρ) ^ q := pow_le_pow_left₀ (by positivity) (by linarith [hθ 1]) q
  have a0 : (1 + |θ 0|) ^ p ≤ (1 + ρ) ^ p := pow_le_pow_left₀ (by positivity) (by linarith [hθ 0]) p
  calc ‖fwdPow θ n q p U‖ = ‖twIter θ 1 n q (twIter θ 0 (n + q) p U)‖ := rfl
    _ ≤ (1 + |θ 1|) ^ q * ‖twIter θ 0 (n + q) p U‖ := h2
    _ ≤ (1 + |θ 1|) ^ q * ((1 + |θ 0|) ^ p * ‖U‖) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (1 + ρ) ^ q * ((1 + ρ) ^ p * ‖U‖) := by gcongr
    _ = (1 + ρ) ^ (p + q) * ‖U‖ := by ring

/-- **Iterated integration by parts** for the twisted power of the stage operator. -/
theorem ibp_pow (θ : Vec 2) (n q p : ℕ) (X : TorusHk (n + q + p) ℂ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (p + q : ℕ) f) (hfp : AVenhance.IsZ2Periodic f) :
    ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y * fibreCovPow (-θ) (p, q) f y =
      (-1 : ℂ) ^ (p + q) * ∫ y in AVenhance.unitCube,
        (torusHkValueCLM (fwdPow θ n q p X) : Vec 2 → ℂ) y * f y := by
  have hg : ContDiff ℝ (p : ℕ) ((fibreCovDeriv (-θ) 1)^[q] f) :=
    contDiff_fibreCovDeriv_iterate (-θ) 1 p q (by simpa [add_comm] using hf)
  have hgp := isZ2Periodic_fibreCovDeriv_iterate (-θ) 1 q hfp
  have h1 := ibp_iter θ 0 (n + q) p X _ hg hgp
  have h2 := ibp_iter θ 1 n q (twIter θ 0 (n + q) p X) f
    (hf.of_le (by exact_mod_cast Nat.le_add_left q p)) hfp
  unfold fibreCovPow
  simp only
  rw [h1, h2, pow_add]
  change _ = _ * ∫ y in AVenhance.unitCube,
    (torusHkValueCLM (twIter θ 1 n q (twIter θ 0 (n + q) p X)) : Vec 2 → ℂ) y * f y
  ring

end AVRegularity.CycleWords.Discard
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleWords.Assembly
open scoped Topology
namespace AVRegularity.CycleWords.Discard

/-! # the pairing of the same-level operator with a smooth periodic test

The pairing `U ↦ ∫ U ψ` against a continuous test is a real-linear bounded functional on
`L²` of the cell (`PrCLM`). With it, the pairing of `sameOp` (with the signs of the
twisted derivatives flipped) against a `C¹` periodic test `φ` is computed from the integration
by parts `torusHk_integration_by_parts` (`sameOp_pair`). -/

/-- The cell pairing with a continuous test as a real-linear bounded functional. -/
def PrCLM (ψ : Vec 2 → ℂ) (hψ : Continuous ψ) :
    ComponentL2 (volume.restrict AVenhance.unitCube) ℂ →L[ℝ] ℂ :=
  (innerSL ℂ ((AVRegularity.CycleComparison.Lift.continuous_cell_memLp _
    (continuous_star.comp hψ) : MemLp (fun y => star (ψ y)) 2
      (volume.restrict AVenhance.unitCube)).toLp (fun y => star (ψ y)))).restrictScalars ℝ

theorem PrCLM_apply (ψ : Vec 2 → ℂ) (hψ : Continuous ψ)
    (u : ComponentL2 (volume.restrict AVenhance.unitCube) ℂ) :
    PrCLM ψ hψ u = ∫ y in AVenhance.unitCube, (u : Vec 2 → ℂ) y * ψ y := by
  have hm : MemLp (fun y => star (ψ y)) 2 (volume.restrict AVenhance.unitCube) :=
    AVRegularity.CycleComparison.Lift.continuous_cell_memLp _ (continuous_star.comp hψ)
  change inner ℂ (hm.toLp (fun y => star (ψ y))) u = _
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hm.coeFn_toLp] with y hy
  rw [hy]
  simp [mul_comm]

theorem pair_integrable (ψ : Vec 2 → ℂ) (hψ : Continuous ψ)
    (u : ComponentL2 (volume.restrict AVenhance.unitCube) ℂ) :
    Integrable (fun y => (u : Vec 2 → ℂ) y * ψ y) (volume.restrict AVenhance.unitCube) :=
  (Lp.memLp u).integrable_mul
    (AVRegularity.CycleComparison.Lift.continuous_cell_memLp _ hψ)

/-- The pairing of the truncation to `H^n`: the same function. -/
theorem pair_trunc (n N : ℕ) (hn : n ≤ N) (X : TorusHk N ℂ) (ψ : Vec 2 → ℂ)
    (hψ : Continuous ψ) :
    PrCLM ψ hψ (torusHkValueCLM (truncateTorusHk hn X)) = PrCLM ψ hψ (torusHkValueCLM X) := by
  rw [torusHkValueCLM_truncate]

/-- The pairing of a twisted derivative of the truncation, by integration by parts. -/
theorem pair_twist (n N : ℕ) (hnN : n + 1 ≤ N) (θ : Vec 2) (k : Fin 2) (X : TorusHk N ℂ)
    (φ : Vec 2 → ℂ) (hφ : ContDiff ℝ 1 φ) (hφp : AVenhance.IsZ2Periodic φ) :
    PrCLM φ hφ.continuous (torusHkValueCLM (tbTwist n θ k (truncateTorusHk hnN X))) =
      -PrCLM (fibreCovDeriv (-θ) k φ)
        (contDiff_fibreCovDeriv (j := 0) (by simpa using hφ) _ k).continuous
        (torusHkValueCLM X) := by
  rw [PrCLM_apply, PrCLM_apply]
  have h := torusHk_integration_by_parts n θ k (truncateTorusHk hnN X) φ hφ hφp
  rw [torusHkValueCLM_truncate] at h
  rw [h, neg_neg]

/-- A real-linear functional of `sameOp`, expanded term by term. -/
theorem sameOp_expand (n N : ℕ) (hnN : n + 1 ≤ N) (θ : Vec 2)
    (M : Fin 2 → TorusHk n ℂ →L[ℝ] TorusHk n ℂ) (a4 a5 : Fin 2 → ℝ) (e123 e4 e5 : ℝ)
    (X : TorusHk N ℂ) (f : TorusHk n ℂ →L[ℝ] ℂ) :
    f (sameOp n N hnN θ M a4 a5 e123 e4 e5 X) =
      (e123 : ℂ) * f (truncateTorusHk (by omega : n ≤ N) X) +
      (e4 : ℂ) * (f (M 0 (truncateTorusHk (by omega : n ≤ N) X)) +
        ((a4 0 : ℂ) * f (tbTwist n θ 0 (truncateTorusHk hnN X)) +
          (a4 1 : ℂ) * f (tbTwist n θ 1 (truncateTorusHk hnN X)))) +
      (e5 : ℂ) * (f (M 1 (truncateTorusHk (by omega : n ≤ N) X)) +
        ((a5 0 : ℂ) * f (tbTwist n θ 0 (truncateTorusHk hnN X)) +
          (a5 1 : ℂ) * f (tbTwist n θ 1 (truncateTorusHk hnN X)))) := by
  have hap : sameOp n N hnN θ M a4 a5 e123 e4 e5 X =
      e123 • truncateTorusHk (by omega : n ≤ N) X +
      e4 • (M 0 (truncateTorusHk (by omega : n ≤ N) X) +
        (a4 0 • tbTwist n θ 0 (truncateTorusHk hnN X) +
          a4 1 • tbTwist n θ 1 (truncateTorusHk hnN X))) +
      e5 • (M 1 (truncateTorusHk (by omega : n ≤ N) X) +
        (a5 0 • tbTwist n θ 0 (truncateTorusHk hnN X) +
          a5 1 • tbTwist n θ 1 (truncateTorusHk hnN X))) := rfl
  rw [hap]
  simp only [map_add, map_smul, Complex.real_smul]

/-- **The pairing of the flipped same-level operator.** -/
theorem sameOp_pair (n N : ℕ) (hnN : n + 1 ≤ N) (θ : Vec 2)
    (M : Fin 2 → TorusHk n ℂ →L[ℝ] TorusHk n ℂ) (v : Vec 2 → Vec 2)
    (hMv : ∀ c U, (torusHkValueCLM (M c U) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => (v x c : ℂ) * torusHkValueCLM U x)
    (a4 a5 : Fin 2 → ℝ) (e123 e4 e5 : ℝ) (X : TorusHk N ℂ) (φ : Vec 2 → ℂ)
    (hφ : ContDiff ℝ 1 φ) (hφp : AVenhance.IsZ2Periodic φ) :
    (∫ y in AVenhance.unitCube,
        (torusHkValueCLM (sameOp n N hnN θ M (fun k => -a4 k) (fun k => -a5 k) e123 e4 e5 X) :
          Vec 2 → ℂ) y * φ y) =
      (e123 : ℂ) * (∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y * φ y) +
      (e4 : ℂ) * ((∫ y in AVenhance.unitCube,
          (torusHkValueCLM X : Vec 2 → ℂ) y * ((v y 0 : ℂ) * φ y)) +
        ((a4 0 : ℂ) * (∫ y in AVenhance.unitCube,
            (torusHkValueCLM X : Vec 2 → ℂ) y * fibreCovDeriv (-θ) 0 φ y) +
          (a4 1 : ℂ) * (∫ y in AVenhance.unitCube,
            (torusHkValueCLM X : Vec 2 → ℂ) y * fibreCovDeriv (-θ) 1 φ y))) +
      (e5 : ℂ) * ((∫ y in AVenhance.unitCube,
          (torusHkValueCLM X : Vec 2 → ℂ) y * ((v y 1 : ℂ) * φ y)) +
        ((a5 0 : ℂ) * (∫ y in AVenhance.unitCube,
            (torusHkValueCLM X : Vec 2 → ℂ) y * fibreCovDeriv (-θ) 0 φ y) +
          (a5 1 : ℂ) * (∫ y in AVenhance.unitCube,
            (torusHkValueCLM X : Vec 2 → ℂ) y * fibreCovDeriv (-θ) 1 φ y))) := by
  have hcφ := hφ.continuous
  have hmul : ∀ c, PrCLM φ hcφ (torusHkValueCLM (M c (truncateTorusHk (by omega : n ≤ N) X)))
      = ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y * ((v y c : ℂ) * φ y) := by
    intro c
    rw [PrCLM_apply]
    refine integral_congr_ae ?_
    have hv : (torusHkValueCLM (truncateTorusHk (by omega : n ≤ N) X) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
        (torusHkValueCLM X : Vec 2 → ℂ) := by rw [torusHkValueCLM_truncate]
    filter_upwards [hMv c (truncateTorusHk (by omega : n ≤ N) X), hv] with y h1 h2
    rw [h1, h2]; ring
  have htw := fun k => pair_twist n N hnN θ k X φ hφ hφp
  have hpr : ∀ U : TorusHk n ℂ, ∫ y in AVenhance.unitCube,
      (torusHkValueCLM U : Vec 2 → ℂ) y * φ y = PrCLM φ hcφ (torusHkValueCLM U) :=
    fun U => (PrCLM_apply φ hcφ _).symm
  refine (hpr _).trans ?_
  have hex := sameOp_expand n N hnN θ M (fun k => -a4 k) (fun k => -a5 k) e123 e4 e5 X
    ((PrCLM φ hcφ).comp (torusHkValueCLM (E := ℂ) (K := n)))
  simp only [ContinuousLinearMap.comp_apply] at hex
  refine hex.trans ?_
  have hA := (pair_trunc n N (by omega : n ≤ N) X φ hcφ).trans (PrCLM_apply φ hcφ _)
  have hT : ∀ k, PrCLM φ hcφ (torusHkValueCLM (tbTwist n θ k (truncateTorusHk hnN X))) =
      -∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y * fibreCovDeriv (-θ) k φ y :=
    fun k => (htw k).trans (congrArg Neg.neg (PrCLM_apply _ _ _))
  simp only [Complex.ofReal_neg]
  have h0 := hmul 0
  have h1 := hmul 1
  have t0 := hT 0
  have t1 := hT 1
  linear_combination (e123 : ℂ) * hA + (e4 : ℂ) * h0 + (e5 : ℂ) * h1 +
    (-(e4 : ℂ) * (a4 0 : ℂ)) * t0 + (-(e4 : ℂ) * (a4 1 : ℂ)) * t1 +
    (-(e5 : ℂ) * (a5 0 : ℂ)) * t0 + (-(e5 : ℂ) * (a5 1 : ℂ)) * t1

end AVRegularity.CycleWords.Discard
end
end
end
