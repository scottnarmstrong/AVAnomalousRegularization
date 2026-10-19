-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.B1WWeightedMember
public import AVRegularity.CycleWords.MixedWords.SharpLetterFactPair
import AVRegularity.CycleWords.MixedWords.ConstituentTransposeStep
import AVRegularity.CycleWords.MixedWords.SharpBlocksSameComm

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # B1.W sharp pass (weighted norm): the blocks of a stage representation

Take a representation of a source sum along the earlier stages,
`X = ∑_{k'<k} ∑_{i'} ⟨W_{i'}, Φ_{i'}⟩`. Every family member is split exactly along the slow test
(`b1w_weighted_member`): `Φ = κ q + φ`, with `φ` actual-fast. The identity is exact, with no
bracket. The stage bounds (`b1w_weighted_blocks`) use the per-stage aggregates of the families:
* the slow pairings `A_s`;
* the sizes `A_f`;
* the defects `A_d`, through `H^{s_{k'}}` realizations of the transverse projection at time `r`.

The bounds are:
* coefficients: `‖κ‖ ≤ A_s/g`;
* weighted remainders: `≤ A_f + Ω A_d + (‖U_q‖ + Ω d_q) A_s/g`. -/

/-- Minkowski with a weight: `x ≤ a + c b` termwise gives
`√∑x² ≤ √∑a² + c√∑b²`. -/
theorem sqrt_sum_le_add_mul {α : Type*} (S : Finset α) (x a b : α → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hx : ∀ i ∈ S, 0 ≤ x i) (hb : ∀ i ∈ S, 0 ≤ b i) (hxab : ∀ i ∈ S, x i ≤ a i + c * b i) :
    Real.sqrt (∑ i ∈ S, x i ^ 2) ≤
      Real.sqrt (∑ i ∈ S, a i ^ 2) + c * Real.sqrt (∑ i ∈ S, b i ^ 2) := by
  refine ((sqrt_sum_sq_le_mul S x (fun i => a i + c * b i) zero_le_one hx
    fun i hi => by rw [one_mul]; exact hxab i hi).trans (le_of_eq (one_mul _))).trans
    ((sqrt_sum_add_sq_le _ _ _).trans (add_le_add le_rfl ?_))
  exact sqrt_sum_sq_le_mul S (fun i => c * b i) b hc (fun i hi => mul_nonneg hc (hb i hi))
    fun _ _ => le_rfl

variable {I : Type*} [Fintype I]

/-- **The weighted blocks of a stage representation.** -/
theorem b1w_weighted_blocks (s : ℕ → ℕ) (Ω : ℕ → ℝ → ℝ) (e : ℝ → Fin 2)
    (tr : ℝ → ComplexCellL2) (r : ℝ) (hΩ : ∀ k', 0 ≤ Ω k' r) (st : I → ℕ) (k : ℕ)
    (W : I → ComplexCellL2) (q : ComplexCellL2) (X : ℂ) (Φ : I → ComplexCellL2)
    (hg : cellComplexPair (tr r + cellConstantCLM 1) q ≠ 0)
    (Uq : ∀ k', TorusHk (s k') ℂ) (hUq : ∀ k' < k, torusHkValueCLM (Uq k') = q)
    (Pw : ∀ k', TorusHk (s k') ℂ →L[ℝ] TorusHk (s k') ℂ)
    (hP : ∀ k' U, torusHkValueCLM (Pw k' U) =
      cellTransverseProjection (e r) (torusHkValueCLM U))
    (hPn : ∀ k' U, ‖Pw k' U‖ ≤ ‖U‖)
    (dq : ℕ → ℝ) (hdq0 : ∀ k', 0 ≤ dq k') (hdq : ∀ k' < k, ‖Uq k' - Pw k' (Uq k')‖ ≤ dq k')
    (UΦ : ∀ k', I → TorusHk (s k') ℂ)
    (hUΦ : ∀ k' < k, ∀ i' ∈ stageSet st k', torusHkValueCLM (UΦ k' i') = Φ i')
    (As Af Ad : ℕ → ℝ)
    (hAs : ∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k',
      ‖cellComplexPair (tr r + cellConstantCLM 1) (Φ i')‖ ^ 2) ≤ As k')
    (hAf : ∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ‖UΦ k' i'‖ ^ 2) ≤ Af k')
    (hAd : ∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ‖UΦ k' i' - Pw k' (UΦ k' i')‖ ^ 2) ≤
      Ad k')
    (hX : X = ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k', cellComplexPair (W i') (Φ i')) :
    ∃ (κ : I → ℂ) (φ : I → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet st k', b1wAdm s tr k' r (φ i')) ∧
      (∀ k' < k, stageNorm st k' κ ≤
        As k' / ‖cellComplexPair (tr r + cellConstantCLM 1) q‖) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', b1wNuW s Ω e k' r (φ i') ^ 2) ≤
        Af k' + Ω k' r * Ad k' + (‖Uq k'‖ + Ω k' r * dq k') *
          (As k' / ‖cellComplexPair (tr r + cellConstantCLM 1) q‖)) ∧
      X = ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
        (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i')) := by
  classical
  have hgpos : 0 < ‖cellComplexPair (tr r + cellConstantCLM 1) q‖ := norm_pos_iff.2 hg
  -- the split of every member, per stage
  have hmem : ∀ k' i', ∃ (κ : ℂ) (φ : ComplexCellL2), k' < k → i' ∈ stageSet st k' →
      b1wAdm s tr k' r φ ∧
      ‖κ‖ = ‖cellComplexPair (tr r + cellConstantCLM 1) (Φ i')‖ /
        ‖cellComplexPair (tr r + cellConstantCLM 1) q‖ ∧
      b1wNuW s Ω e k' r φ ≤ ‖UΦ k' i'‖ + ‖κ‖ * ‖Uq k'‖ +
        Ω k' r * (‖UΦ k' i' - Pw k' (UΦ k' i')‖ + ‖κ‖ * ‖Uq k' - Pw k' (Uq k')‖) ∧
      ∀ Wv : ComplexCellL2, cellComplexPair Wv (Φ i') =
        star κ * cellComplexPair Wv q + cellComplexPair Wv φ := by
    intro k' i'
    by_cases h : k' < k ∧ i' ∈ stageSet st k'
    · obtain ⟨hk', hi'⟩ := h
      obtain ⟨κ, φ, h1, h2, h3, h4⟩ := b1w_weighted_member s Ω e tr k' r (hΩ k') (Pw k')
        (hP k') (hPn k') q (Uq k') (hUq k' hk') hg (Φ i') (UΦ k' i') (hUΦ k' hk' i' hi')
      exact ⟨κ, φ, fun _ _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨0, 0, fun hk' hi' => absurd ⟨hk', hi'⟩ h⟩
  choose κs φs hκφ using hmem
  have hst : ∀ k' i', i' ∈ stageSet st k' → st i' = k' := fun k' i' hi' =>
    (Finset.mem_filter.1 hi').2
  -- the coefficients, per stage
  have hκst : ∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ‖κs k' i'‖ ^ 2) ≤
      As k' / ‖cellComplexPair (tr r + cellConstantCLM 1) q‖ := by
    intro k' hk'
    have h := sqrt_sum_sq_le_mul (stageSet st k') (fun i' => ‖κs k' i'‖)
      (fun i' => ‖cellComplexPair (tr r + cellConstantCLM 1) (Φ i')‖)
      (c := 1 / ‖cellComplexPair (tr r + cellConstantCLM 1) q‖) (by positivity)
      (fun _ _ => norm_nonneg _) fun i' hi' => by
        rw [(hκφ k' i' hk' hi').2.1, one_div_mul_eq_div]
    refine h.trans ?_
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (hAs k' hk') hgpos.le
  refine ⟨fun i' => star (κs (st i') i'), fun i' => φs (st i') i', ?_, ?_, ?_, ?_⟩
  · intro k' hk' i' hi'
    show b1wAdm s tr k' r (φs (st i') i')
    rw [hst k' i' hi']
    exact (hκφ k' i' hk' hi').1
  · intro k' hk'
    unfold stageNorm
    have hsum : ∑ i' ∈ stageSet st k', ‖star (κs (st i') i')‖ ^ 2 =
        ∑ i' ∈ stageSet st k', ‖κs k' i'‖ ^ 2 :=
      Finset.sum_congr rfl fun i' hi' => by rw [hst k' i' hi', norm_star]
    rw [hsum]
    exact hκst k' hk'
  · intro k' hk'
    have hsum : ∑ i' ∈ stageSet st k', b1wNuW s Ω e k' r (φs (st i') i') ^ 2 =
        ∑ i' ∈ stageSet st k', b1wNuW s Ω e k' r (φs k' i') ^ 2 :=
      Finset.sum_congr rfl fun i' hi' => by rw [hst k' i' hi']
    rw [hsum]
    have hΩk := hΩ k'
    -- the sizes and the defects of the members
    have hA : Real.sqrt (∑ i' ∈ stageSet st k',
        (‖UΦ k' i'‖ + Ω k' r * ‖UΦ k' i' - Pw k' (UΦ k' i')‖) ^ 2) ≤ Af k' + Ω k' r * Ad k' :=
      (sqrt_sum_le_add_mul (stageSet st k') _ (fun i' => ‖UΦ k' i'‖)
        (fun i' => ‖UΦ k' i' - Pw k' (UΦ k' i')‖) (Ω k' r) hΩk
        (fun i' _ => add_nonneg (norm_nonneg _) (mul_nonneg hΩk (norm_nonneg _)))
        (fun _ _ => norm_nonneg _) fun _ _ => le_rfl).trans
        (add_le_add (hAf k' hk') (mul_le_mul_of_nonneg_left (hAd k' hk') hΩk))
    refine (sqrt_sum_le_add_mul (stageSet st k') (fun i' => b1wNuW s Ω e k' r (φs k' i'))
      (fun i' => ‖UΦ k' i'‖ + Ω k' r * ‖UΦ k' i' - Pw k' (UΦ k' i')‖)
      (fun i' => ‖κs k' i'‖) (‖Uq k'‖ + Ω k' r * dq k')
      (add_nonneg (norm_nonneg _) (mul_nonneg hΩk (hdq0 k')))
      (fun i' _ => b1wNuW_nonneg s Ω e k' r hΩk _) (fun _ _ => norm_nonneg _)
      fun i' hi' => ?_).trans (add_le_add hA (mul_le_mul_of_nonneg_left (hκst k' hk')
        (add_nonneg (norm_nonneg _) (mul_nonneg hΩk (hdq0 k')))))
    refine (hκφ k' i' hk' hi').2.2.1.trans ?_
    have h1 : ‖κs k' i'‖ * ‖Uq k' - Pw k' (Uq k')‖ ≤ ‖κs k' i'‖ * dq k' :=
      mul_le_mul_of_nonneg_left (hdq k' hk') (norm_nonneg _)
    have h2 := mul_le_mul_of_nonneg_left h1 hΩk
    nlinarith [norm_nonneg (κs k' i')]
  · rw [hX]
    refine Finset.sum_congr rfl fun k' hk' => Finset.sum_congr rfl fun i' hi' => ?_
    show cellComplexPair (W i') (Φ i') = star (κs (st i') i') * cellComplexPair (W i') q +
      cellComplexPair (W i') (φs (st i') i')
    rw [hst k' i' hi']
    exact (hκφ k' i' (Finset.mem_range.1 hk') hi').2.2.2 (W i')

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # the letter unit terms commute with the transverse projection

`CommRep e N n G` says that the functional `G` of the classical representative is realized by a
real-linear map `H^N → H^n` that commutes with the transverse projection of the orientation `e`
(the projection at each level is the one of `transverseHsProjection`). It is closed under sums
and real multiples, and contains the unit terms `κ D_θ^{(p,q)}(c f)`, `κ D_θ^{(p,q)}(c D_{θ,k} f)`
with `c` invariant along `e`. -/

local instance sharpLetterUnitsTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
local instance sharpLetterUnitsTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
local instance sharpLetterUnitsTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance

/-- The transverse projection of `H^s` (a chosen realization). -/
def commProj (e : Fin 2) (s : ℕ) : TorusHk s ℂ →L[ℝ] TorusHk s ℂ :=
  Classical.choose (transverseHsProjection e s)

theorem commProj_value (e : Fin 2) (s : ℕ) (U : TorusHk s ℂ) :
    torusHkValueCLM (commProj e s U) = cellTransverseProjection e (torusHkValueCLM U) :=
  (Classical.choose_spec (transverseHsProjection e s)).1 U

/-- A functional of the classical representative realized by a map commuting with the projection. -/
def CommRep (e : Fin 2) (N n : ℕ) (G : (Vec 2 → ℂ) → Vec 2 → ℂ) : Prop :=
  ∃ A : TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
    (∀ ψ, (torusHkValueCLM (A ψ) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      G (torusHigherClassicalValue N ψ)) ∧
    ∀ ψ, commProj e n (A ψ) = A (commProj e N ψ)

section Closure

variable {e : Fin 2} {N n : ℕ} {G G' : (Vec 2 → ℂ) → Vec 2 → ℂ}

theorem CommRep.zero : CommRep e N n (fun _ _ => 0) :=
  ⟨0, fun ψ => by
    rw [zero_apply, map_zero]; exact Lp.coeFn_zero _ _ _,
    fun ψ => by simp⟩

theorem CommRep.congr (h : CommRep e N n G)
    (hG : ∀ ψ : TorusHk N ℂ, G (torusHigherClassicalValue N ψ) =
      G' (torusHigherClassicalValue N ψ)) : CommRep e N n G' := by
  obtain ⟨A, hv, hc⟩ := h
  exact ⟨A, fun ψ => by rw [← hG ψ]; exact hv ψ, hc⟩

theorem CommRep.add (h : CommRep e N n G) (h' : CommRep e N n G') :
    CommRep e N n (fun f z => G f z + G' f z) := by
  obtain ⟨A, hv, hc⟩ := h
  obtain ⟨A', hv', hc'⟩ := h'
  refine ⟨A + A', fun ψ => ?_, fun ψ => ?_⟩
  · rw [add_apply, map_add]
    filter_upwards [Lp.coeFn_add (torusHkValueCLM (A ψ)) (torusHkValueCLM (A' ψ)), hv ψ, hv' ψ]
      with z h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
  · rw [add_apply, add_apply, map_add, hc, hc']

theorem CommRep.smul (h : CommRep e N n G) (a : ℝ) :
    CommRep e N n (fun f z => (a : ℂ) * G f z) := by
  obtain ⟨A, hv, hc⟩ := h
  refine ⟨lrSmul a A, fun ψ => ?_, fun ψ => ?_⟩
  · rw [lrSmul_apply, map_smul]
    filter_upwards [Lp.coeFn_smul a (torusHkValueCLM (A ψ)), hv ψ] with z h1 h2
    rw [h1]
    simp only [Pi.smul_apply, h2, Complex.real_smul]
  · rw [lrSmul_apply, lrSmul_apply, map_smul, hc]

theorem CommRep.finset_sum {κ : Type*} (s : Finset κ) {G : κ → (Vec 2 → ℂ) → Vec 2 → ℂ}
    (h : ∀ j ∈ s, CommRep e N n (G j)) : CommRep e N n (fun f z => ∑ j ∈ s, G j f z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CommRep.zero (e := e) (N := N) (n := n))
  | insert a s ha ih =>
    have := (h a (Finset.mem_insert_self a s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert ha] using this

theorem CommRep.list_sum {κ : Type*} (l : List κ) {G : κ → (Vec 2 → ℂ) → Vec 2 → ℂ}
    (h : ∀ j ∈ l, CommRep e N n (G j)) : CommRep e N n (fun f z => (l.map fun j => G j f z).sum) := by
  induction l with
  | nil => simpa using (CommRep.zero (e := e) (N := N) (n := n))
  | cons a l ih =>
    have := (h a List.mem_cons_self).add (ih fun j hj => h j (List.mem_cons_of_mem _ hj))
    simpa using this

end Closure

section Units

theorem commTw (θ : Vec 2) (k e : Fin 2) (K : ℕ) :
    ∀ (m : ℕ) (U : TorusHk (K + m) ℂ),
      commProj e K (twIter θ k K m U) = twIter θ k K m (commProj e (K + m) U)
  | 0, U => rfl
  | m + 1, U => by
    have ih := commTw θ k e K m (tbTwist (K + m) θ k U)
    have hc := comm_twist (K + m) e k θ (commProj e (K + m)) (commProj_value e (K + m)) U
      (commProj e (K + m + 1) U) (commProj_value e (K + m + 1) U)
    change commProj e K (twIter θ k K m (tbTwist (K + m) θ k U)) =
      twIter θ k K m (tbTwist (K + m) θ k (commProj e (K + m + 1) U))
    rw [ih, hc]

theorem comm_unitOp (θ : Vec 2) (n p q : ℕ) (e : Fin 2) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ}
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P)
    (ht : ∀ (z : Vec 2) (s : ℝ), c (z + s • basisVec e) = c z) (U : TorusHk (n + p + q) ℂ) :
    commProj e n (unitOp θ n p q hc hp hP U) = unitOp θ n p q hc hp hP (commProj e (n + p + q) U) := by
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP 0 (Nat.zero_le _) 0)
  have hb : ∀ x, |c x| ≤ P := fun x => by
    have := hP 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hm := comm_mul e (commProj e (n + p + q)) (commProj_value e _) c hc.continuous hp ht P hP0 hb
    (tbMulCLM (n + p + q) hc hp hP) (tbMulCLM_value_ae (n + p + q) hc hp hP) U
    (commProj e (n + p + q) U) (commProj_value e _ U)
  change commProj e n (twIter θ 0 n p (twIter θ 1 (n + p) q (tbMulCLM (n + p + q) hc hp hP U))) =
    twIter θ 0 n p (twIter θ 1 (n + p) q (tbMulCLM (n + p + q) hc hp hP (commProj e (n + p + q) U)))
  rw [commTw θ 0 e n p, commTw θ 1 e (n + p) q, hm]

private theorem commUnit_classical (N p q : ℕ) (h2 : p + q + 3 ≤ N) (ψ : TorusHk N ℂ) :
    ContDiff ℝ ((p + q + 1 : ℕ) : ℕ∞) (torusHigherClassicalValue N ψ) ∧
      (torusHkValueCLM ψ : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
        torusHigherClassicalValue N ψ :=
  ⟨torusHigherClassicalValue_contDiff N (p + q + 1) (by omega) ψ,
    (torusHigherClassicalValue_ae N (by omega) ψ).symm⟩

/-- **Unit term, no extra derivative, commuting with the projection.** -/
theorem commRep_unit0 (e : Fin 2) (θ : Vec 2) (n N p q : ℕ)
    (h1 : n + p + q ≤ N) (h2 : p + q + 3 ≤ N) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ}
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P)
    (ht : ∀ (z : Vec 2) (s : ℝ), c (z + s • basisVec e) = c z) (κ : ℝ) :
    CommRep e N n (fun f z => (κ : ℂ) * fibreCovPow θ (p, q) (fun y => (c y : ℂ) * f y) z) := by
  refine ⟨lrSmul κ ((unitOp θ n p q hc hp hP).comp (truncateTorusHk h1)), fun ψ => ?_,
    fun ψ => ?_⟩
  · obtain ⟨hcd, hae⟩ := commUnit_classical N p q h2 ψ
    have hv : (torusHkValueCLM (truncateTorusHk h1 ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] torusHigherClassicalValue N ψ := hae
    have hcp : ContDiff ℝ (p + q : ℕ) (fun x => (c x : ℂ) * torusHigherClassicalValue N ψ x) :=
      contDiff_real_mul_complex (hc.of_le (by exact_mod_cast (by omega : p + q ≤ n + p + q)))
        (hcd.of_le (by exact_mod_cast (by omega : p + q ≤ p + q + 1)))
    have := unitOp_value θ n p q hc hp hP (truncateTorusHk h1 ψ) _ hcp hv
    rw [lrSmul_apply, map_smul]
    filter_upwards [Lp.coeFn_smul κ (torusHkValueCLM (unitOp θ n p q hc hp hP
      (truncateTorusHk h1 ψ))), this] with z e1 e2
    rw [ContinuousLinearMap.comp_apply, e1]
    simp only [Pi.smul_apply, e2, Complex.real_smul]
  · rw [lrSmul_apply, lrSmul_apply, map_smul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, comm_unitOp θ n p q e hc hp hP ht,
      comm_trunc h1 e (commProj e N) (commProj e (n + p + q)) (commProj_value e N)
        (commProj_value e _)]

/-- **Unit term with one extra twisted derivative, commuting with the projection.** -/
theorem commRep_unit1 (e : Fin 2) (θ : Vec 2) (n N p q : ℕ) (k : Fin 2)
    (h1 : n + p + q + 1 ≤ N) (h2 : p + q + 3 ≤ N) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ}
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P)
    (ht : ∀ (z : Vec 2) (s : ℝ), c (z + s • basisVec e) = c z) (κ : ℝ) :
    CommRep e N n (fun f z => (κ : ℂ) * fibreCovPow θ (p, q)
        (fun y => (c y : ℂ) * fibreCovDeriv θ k f y) z) := by
  refine ⟨lrSmul κ ((unitOp θ n p q hc hp hP).comp
    ((tbTwist (n + p + q) θ k).comp (truncateTorusHk h1))), fun ψ => ?_, fun ψ => ?_⟩
  · obtain ⟨hcd, hae⟩ := commUnit_classical N p q h2 ψ
    have hv : (torusHkValueCLM (truncateTorusHk h1 ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] torusHigherClassicalValue N ψ := hae
    have hc1 : ContDiff ℝ 1 (torusHigherClassicalValue N ψ) :=
      hcd.of_le (by exact_mod_cast (by omega : 1 ≤ p + q + 1))
    have hD := tbTwist_value_ae (n + p + q) θ k (truncateTorusHk h1 ψ) _ hc1 hv
    have hcd' : ContDiff ℝ (p + q : ℕ) (fibreCovDeriv θ k (torusHigherClassicalValue N ψ)) :=
      contDiff_fibreCovDeriv (j := p + q) hcd θ k
    have hcp : ContDiff ℝ (p + q : ℕ)
        (fun x => (c x : ℂ) * fibreCovDeriv θ k (torusHigherClassicalValue N ψ) x) :=
      contDiff_real_mul_complex (hc.of_le (by exact_mod_cast (by omega : p + q ≤ n + p + q))) hcd'
    have := unitOp_value θ n p q hc hp hP (tbTwist (n + p + q) θ k (truncateTorusHk h1 ψ)) _ hcp hD
    rw [lrSmul_apply, map_smul]
    filter_upwards [Lp.coeFn_smul κ (torusHkValueCLM (unitOp θ n p q hc hp hP
      (tbTwist (n + p + q) θ k (truncateTorusHk h1 ψ)))), this] with z e1 e2
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, e1]
    simp only [Pi.smul_apply, e2, Complex.real_smul]
  · have hT := comm_twist (n + p + q) e k θ (commProj e (n + p + q)) (commProj_value e _)
      (truncateTorusHk h1 ψ) (commProj e (n + p + q + 1) (truncateTorusHk h1 ψ))
      (commProj_value e _ _)
    have hTr := comm_trunc h1 e (commProj e N) (commProj e (n + p + q + 1)) (commProj_value e N)
      (commProj_value e _) ψ
    simp only [lrSmul_apply, map_smul, ContinuousLinearMap.comp_apply]
    rw [comm_unitOp θ n p q e hc hp hP ht, hT, hTr]

end Units

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # B1.W sharp pass (weighted norm): H3s at one time, in the form of the abstract fibre word

The stage representation with the sharp families (`b1w_sharp_repr_at`) is split exactly along the
slow test (`b1w_weighted_blocks`). The remainders lie in the crude admissible class and are
measured by the weighted norm `b1wNuW s Ω e`. The defects are charged to `Ω`:
* where `Ω_{k'}(r) > 1`, a least window of orientation `e(r)` exists (`hwin`, from the activity
  lemma), and the window clause of the families gives `Ω A_d ≤ B·Ω‖w − P_N w‖‖β‖`;
* elsewhere `A_d ≤ 2A_f`.

With `|E_q| ≤ c_E|E|`, `‖U_q‖ ≤ C_w|E|`, `Ω‖w − P_N w‖ ≤ ζ|E|` and `Ω‖U_q − PU_q‖ ≤ |E|`
(where `Ω > 1`), the coefficients are `≤ Θζ²‖β‖` and the weighted remainders are `≤ Θζ|E|‖β‖`,
with `Θ = b1wWeightedΘ = B(1 + c_E)(5 + 3C_w)` (shared with the H4 decomposition). The identity is
exact, so this source contributes no error (`b1w_weighted_H3s_at`). -/

universe u v

/-- The constant of the weighted H3s. -/
def b1wWeightedΘ (B cE Cw : ℝ) : ℝ := B * (1 + cE) * (5 + 3 * Cw)

/-- The remainder algebra of the weighted H3s. -/
theorem weighted_rem_le {B ζ En sβ cE Cw Af ΩAd Uqd As : ℝ} (hB : 0 ≤ B) (hζ0 : 0 ≤ ζ)
    (hζ1 : ζ ≤ 1) (hEn : 0 ≤ En) (hsβ : 0 ≤ sβ) (hcE : 0 ≤ cE) (hCw : 0 ≤ Cw)
    (hAf : Af ≤ B * ζ * (cE * En) * sβ) (hAd : ΩAd ≤ B * ζ * En * sβ * (1 + 2 * cE))
    (hUq : Uqd ≤ (3 * Cw + 1) * En) (hAs0 : 0 ≤ As)
    (hAs : As ≤ B * cE * ζ ^ 2 * sβ) :
    Af + ΩAd + Uqd * As ≤ b1wWeightedΘ B cE Cw * ζ * En * sβ := by
  have hζ2 : ζ ^ 2 ≤ ζ := by nlinarith
  have hAs' : As ≤ B * cE * ζ * sβ := hAs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hζ2 (mul_nonneg hB hcE)) hsβ)
  have h3 : Uqd * As ≤ (3 * Cw + 1) * En * (B * cE * ζ * sβ) :=
    mul_le_mul hUq hAs' hAs0 (by positivity)
  have hX : 0 ≤ B * ζ * En * sβ := by positivity
  have hsum : Af + ΩAd + Uqd * As ≤ B * ζ * En * sβ * (1 + 4 * cE + 3 * Cw * cE) := by
    have e1 : B * ζ * (cE * En) * sβ = B * ζ * En * sβ * cE := by ring
    have e3 : (3 * Cw + 1) * En * (B * cE * ζ * sβ) = B * ζ * En * sβ * ((3 * Cw + 1) * cE) := by
      ring
    nlinarith
  have hc : 1 + 4 * cE + 3 * Cw * cE ≤ (1 + cE) * (5 + 3 * Cw) := by
    nlinarith [mul_nonneg hCw hcE]
  calc Af + ΩAd + Uqd * As ≤ B * ζ * En * sβ * (1 + 4 * cE + 3 * Cw * cE) := hsum
    _ ≤ B * ζ * En * sβ * ((1 + cE) * (5 + 3 * Cw)) := mul_le_mul_of_nonneg_left hc hX
    _ = b1wWeightedΘ B cE Cw * ζ * En * sβ := by unfold b1wWeightedΘ; ring

/-- The defect of a family of scalar multiples of one test. -/
theorem scalar_family_defect {I : Type*} (S : Finset I) {N : ℕ} (e : Fin 2) (c : I → ℂ)
    (w : TorusHk N ℂ) (PN : TorusHk N ℂ →L[ℝ] TorusHk N ℂ)
    (hPN : ∀ U, torusHkValueCLM (PN U) = cellTransverseProjection e (torusHkValueCLM U)) :
    ∑ i ∈ S, ‖torusHigherScalarCLM N (c i) w - PN (torusHigherScalarCLM N (c i) w)‖ ^ 2 =
      ‖w - PN w‖ ^ 2 * ∑ i ∈ S, ‖c i‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : PN (torusHigherScalarCLM N (c i) w) = torusHigherScalarCLM N (c i) (PN w) :=
    torusHk_projection_scalar e PN hPN (c i) w
  have h2 : torusHigherScalarCLM N (c i) w - torusHigherScalarCLM N (c i) (PN w) =
      torusHigherScalarCLM N (c i) (w - PN w) := (map_sub _ _ _).symm
  rw [h1, h2, torusHigherScalarCLM_norm, mul_pow, mul_comm]

/-- The defect term of the weighted H3s, at one stage. -/
theorem weighted_stage_defect {I : Type*} (S : Finset I) {n : ℕ} (U : I → TorusHk n ℂ)
    (P : TorusHk n ℂ →L[ℝ] TorusHk n ℂ) (hPn : ∀ V, ‖P V‖ ≤ ‖V‖) {Ω B ζ En sβ cE δ : ℝ}
    (hΩ : 0 ≤ Ω) (hB : 0 ≤ B) (hζ : 0 ≤ ζ) (hEn : 0 ≤ En) (hsβ : 0 ≤ sβ) (hcE : 0 ≤ cE)
    (hwin : 1 < Ω → ∑ i ∈ S, ‖U i - P (U i)‖ ^ 2 ≤ B ^ 2 * (δ ^ 2 * sβ ^ 2))
    (hδ0 : 0 ≤ δ) (hδ : 1 < Ω → Ω * δ ≤ ζ * En)
    (hAf : Real.sqrt (∑ i ∈ S, ‖U i‖ ^ 2) ≤ B * ζ * (cE * En) * sβ) :
    Ω * Real.sqrt (∑ i ∈ S, ‖U i - P (U i)‖ ^ 2) ≤ B * ζ * En * sβ * (1 + 2 * cE) := by
  have hX : 0 ≤ B * ζ * En * sβ := mul_nonneg (mul_nonneg (mul_nonneg hB hζ) hEn) hsβ
  have hS0 := Real.sqrt_nonneg (∑ i ∈ S, ‖U i - P (U i)‖ ^ 2)
  by_cases hΩ1 : 1 < Ω
  · have hsq : Real.sqrt (∑ i ∈ S, ‖U i - P (U i)‖ ^ 2) ≤ B * δ * sβ := by
      refine (Real.sqrt_le_sqrt (hwin hΩ1)).trans_eq ?_
      rw [show B ^ 2 * (δ ^ 2 * sβ ^ 2) = (B * δ * sβ) ^ 2 by ring]
      exact Real.sqrt_sq (mul_nonneg (mul_nonneg hB hδ0) hsβ)
    have h1 := mul_le_mul_of_nonneg_left hsq hΩ
    have h2 := mul_le_mul_of_nonneg_left (hδ hΩ1) (mul_nonneg hB hsβ)
    have e1 : Ω * (B * δ * sβ) = B * sβ * (Ω * δ) := by ring
    have e2 : B * sβ * (ζ * En) = B * ζ * En * sβ := by ring
    nlinarith
  · push Not at hΩ1
    have hsq : Real.sqrt (∑ i ∈ S, ‖U i - P (U i)‖ ^ 2) ≤ 2 * Real.sqrt (∑ i ∈ S, ‖U i‖ ^ 2) :=
      sqrt_sum_sq_le_mul _ _ _ zero_le_two (fun _ _ => norm_nonneg _) fun i _ =>
        (norm_sub_le _ _).trans (by linarith [hPn (U i)])
    have h1 : Ω * Real.sqrt (∑ i ∈ S, ‖U i - P (U i)‖ ^ 2) ≤
        Real.sqrt (∑ i ∈ S, ‖U i - P (U i)‖ ^ 2) := by nlinarith
    have e1 : B * ζ * (cE * En) * sβ = B * ζ * En * sβ * cE := by ring
    nlinarith

/-- The slow-test term of the weighted H3s, at one stage. -/
theorem weighted_uq_le {n : ℕ} (Uq : TorusHk n ℂ) (P : TorusHk n ℂ →L[ℝ] TorusHk n ℂ)
    (hPn : ∀ V, ‖P V‖ ≤ ‖V‖) {Ω Cw En : ℝ} (hCw : 0 ≤ Cw) (hEn : 0 ≤ En)
    (hU : ‖Uq‖ ≤ Cw * En) (hq : 1 < Ω → Ω * ‖Uq - P Uq‖ ≤ En) :
    ‖Uq‖ + Ω * ‖Uq - P Uq‖ ≤ (3 * Cw + 1) * En := by
  by_cases hΩ1 : 1 < Ω
  · have := hq hΩ1
    nlinarith [mul_nonneg hCw hEn]
  · push Not at hΩ1
    have hd : ‖Uq - P Uq‖ ≤ 2 * ‖Uq‖ := (norm_sub_le _ _).trans (by linarith [hPn Uq])
    have : Ω * ‖Uq - P Uq‖ ≤ ‖Uq - P Uq‖ := by nlinarith [norm_nonneg (Uq - P Uq)]
    nlinarith [mul_nonneg hCw hEn]

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The weighted H3s at one time, in the form of the abstract fibre word.** -/
theorem b1w_weighted_H3s_at {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (k : ℕ) (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (s : ℕ → ℕ) (n N : ℕ) (hN : n + 3 ≤ N)
    (W S : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (Fl : B1WIndex ι h Nw m Ks → Fin 2 → ComplexCellL2) (q : ComplexCellL2)
    (qs : TorusHk 1 ℂ) (w : TorusHk N ℂ) (hwq : torusHkValueCLM w = q)
    (hqs : torusHkValueCLM qs = q)
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
    (B M₀ : ℝ)
    (hprov : ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ, ∀ k' < k,
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
        B1WSharpFamily F θ r k k' N (s k') ψ Φ B M₀)
    (hB : 0 ≤ B) (tr : ℝ → ComplexCellL2) (Ω : ℕ → ℝ → ℝ) (e : ℝ → Fin 2)
    (hΩ0 : ∀ k', 0 ≤ Ω k' r)
    (Eq : ℂ) (Dd : TorusHk N ℂ) (hw : w = torusHigherConstant N Eq + Dd)
    (hDd : ‖Dd‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ) * ‖Eq‖)
    (htr : ‖tr r‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ))
    (E : ℂ) (hE : cellComplexPair (tr r + cellConstantCLM 1) q = E) (hE0 : E ≠ 0)
    (cE Cw : ℝ) (hcE : 0 ≤ cE) (hCw : 0 ≤ Cw) (hEq : ‖Eq‖ ≤ cE * ‖E‖)
    (Uq : ∀ k', TorusHk (s k') ℂ) (hUq : ∀ k' < k, torusHkValueCLM (Uq k') = q)
    (hUqn : ∀ k' < k, ‖Uq k'‖ ≤ Cw * ‖E‖)
    (PN : TorusHk N ℂ →L[ℝ] TorusHk N ℂ)
    (hPN : ∀ U, torusHkValueCLM (PN U) = cellTransverseProjection (e r) (torusHkValueCLM U))
    (Pw : ∀ k', TorusHk (s k') ℂ →L[ℝ] TorusHk (s k') ℂ)
    (hP : ∀ k' U, torusHkValueCLM (Pw k' U) =
      cellTransverseProjection (e r) (torusHkValueCLM U))
    (hPn : ∀ k' U, ‖Pw k' U‖ ≤ ‖U‖)
    (hwin : ∀ k' < k, 1 < Ω k' r → ∃ p, IsLeastWindow F.reg p r ∧ F.reg.orient p = e r)
    (hΩw : ∀ k' < k, 1 < Ω k' r → Ω k' r * ‖w - PN w‖ ≤
      min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) * ‖E‖)
    (hΩq : ∀ k' < k, 1 < Ω k' r → Ω k' r * ‖Uq k' - Pw k' (Uq k')‖ ≤ ‖E‖)
    (N₀ : ℂ) (Γr : ℝ) (hNΓ : ‖N₀‖ * Γr = ‖E‖)
    (β : B1WIndex ι h Nw m Ks → ℂ) :
    ∃ (κ : B1WIndex ι h Nw m Ks → ℂ) (φ : B1WIndex ι h Nw m Ks → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet b1wSt k', b1wAdm s tr k' r (φ i')) ∧
      (∀ k' < k, stageNorm b1wSt k' κ ≤ b1wWeightedΘ B cE Cw *
        min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) ^ 2 *
          stageNorm b1wSt k β) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', b1wNuW s Ω e k' r (φ i') ^ 2) ≤
        b1wWeightedΘ B cE Cw *
          min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) *
            (‖N₀‖ * Γr) * stageNorm b1wSt k β) ∧
      ∑ i ∈ stageSet b1wSt k, β i * cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) qs =
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k',
          (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i')) := by
  classical
  obtain ⟨UΦ, Φall, hUΦval, hfam, hrep⟩ := b1w_sharp_repr_at F θ r k hπ hϖ s n N hN W S Fl q
    qs w hwq hqs hS hF hExp hearly hW B M₀ hprov β
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = fibreNorm (planeFibreFrequency F.η θ) := ⟨_, rfl⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ, ζ = min 1 (x + (Real.sqrt F.S)⁻¹) := ⟨_, rfl⟩
  obtain ⟨sβ, hsβ⟩ : ∃ sβ : ℝ, sβ = stageNorm b1wSt k β := ⟨_, rfl⟩
  rw [← hx] at hDd htr hΩw
  rw [← hζ] at hΩw
  rw [← hx, ← hζ, ← hsβ, hNΓ]
  have hEpos : 0 < ‖E‖ := norm_pos_iff.2 hE0
  have hg : cellComplexPair (tr r + cellConstantCLM 1) q ≠ 0 := by rw [hE]; exact hE0
  have hx0 : 0 ≤ x := hx ▸ fibreNorm_nonneg _
  have hζ0 : 0 ≤ ζ := hζ ▸ le_min zero_le_one (add_nonneg hx0 (inv_nonneg.2 (Real.sqrt_nonneg _)))
  have hζ1 : ζ ≤ 1 := hζ ▸ min_le_left _ _
  have hsβ0 : 0 ≤ sβ := hsβ ▸ stageNorm_nonneg _ _ _
  have hβsum : ∑ i ∈ stageSet b1wSt k, ‖star (β i)‖ ^ 2 = sβ ^ 2 := by
    rw [hsβ]
    unfold stageNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun i _ => by rw [norm_star]
  -- the slow facts of the families
  have hslow : ∀ k' (hk' : k' < k),
      (∀ R : ComplexCellL2, ‖R‖ ≤ M₀ * x →
        ∑ i' ∈ stageSet b1wSt k',
          ‖cellComplexPair (R + cellConstantCLM 1) (torusHkValueCLM (UΦ k' i'))‖ ^ 2 ≤
          B ^ 2 * ζ ^ 4 * ‖Eq‖ ^ 2 * sβ ^ 2) ∧
      ∑ i' ∈ stageSet b1wSt k', ‖UΦ k' i'‖ ^ 2 ≤ B ^ 2 * ζ ^ 2 * ‖Eq‖ ^ 2 * sβ ^ 2 := by
    intro k' hk'
    have hf := (hfam k' hk').2.2.1
    rw [← hx, ← hζ] at hf
    have h := hf.2 Eq (fun i => star (β i)) Dd hDd (fun i _ => by rw [hw])
    rw [hβsum] at h
    exact h
  have hAs : ∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k',
      ‖cellComplexPair (tr r + cellConstantCLM 1) (Φall i')‖ ^ 2) ≤ B * ζ ^ 2 * ‖Eq‖ * sβ := by
    intro k' hk'
    rw [Finset.sum_congr rfl fun i' hi' => by rw [← hUΦval k' hk' i' hi']]
    refine (Real.sqrt_le_sqrt ((hslow k' hk').1 (tr r) htr)).trans_eq ?_
    rw [show B ^ 2 * ζ ^ 4 * ‖Eq‖ ^ 2 * sβ ^ 2 = (B * ζ ^ 2 * ‖Eq‖ * sβ) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hAf : ∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', ‖UΦ k' i'‖ ^ 2) ≤
      B * ζ * ‖Eq‖ * sβ := by
    intro k' hk'
    refine (Real.sqrt_le_sqrt (hslow k' hk').2).trans_eq ?_
    rw [show B ^ 2 * ζ ^ 2 * ‖Eq‖ ^ 2 * sβ ^ 2 = (B * ζ * ‖Eq‖ * sβ) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  -- the weighted blocks
  obtain ⟨κ, φ, hadm, hκb, hνb, hid⟩ := b1w_weighted_blocks s Ω e tr r hΩ0 b1wSt k W q _ Φall
    hg Uq hUq Pw hP hPn (fun k' => ‖Uq k' - Pw k' (Uq k')‖) (fun _ => norm_nonneg _)
    (fun _ _ => le_rfl) UΦ hUΦval (fun _ => B * ζ ^ 2 * ‖Eq‖ * sβ) (fun _ => B * ζ * ‖Eq‖ * sβ)
    (fun k' => Real.sqrt (∑ i' ∈ stageSet b1wSt k', ‖UΦ k' i' - Pw k' (UΦ k' i')‖ ^ 2))
    hAs hAf (fun _ _ => le_rfl) hrep
  rw [hE] at hκb hνb
  have hAsE : B * ζ ^ 2 * ‖Eq‖ * sβ / ‖E‖ ≤ B * cE * ζ ^ 2 * sβ := by
    rw [div_le_iff₀ hEpos]
    have := mul_le_mul_of_nonneg_left hEq (by positivity : (0 : ℝ) ≤ B * ζ ^ 2 * sβ)
    nlinarith
  have hBζ : 0 ≤ B * ζ := mul_nonneg hB hζ0
  have hAs0 : 0 ≤ B * ζ ^ 2 * ‖Eq‖ * sβ :=
    mul_nonneg (mul_nonneg (mul_nonneg hB (sq_nonneg ζ)) (norm_nonneg Eq)) hsβ0
  refine ⟨κ, φ, hadm, fun k' hk' => (hκb k' hk').trans (hAsE.trans ?_), fun k' hk' => ?_, hid⟩
  · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)) hsβ0
    unfold b1wWeightedΘ
    nlinarith [mul_nonneg hB hcE, mul_nonneg (mul_nonneg hB hcE) hCw, mul_nonneg hB hCw]
  · refine (hνb k' hk').trans ?_
    have hΩk := hΩ0 k'
    have hAd := weighted_stage_defect (stageSet b1wSt k') (UΦ k') (Pw k') (hPn k') hΩk hB hζ0
      hEpos.le hsβ0 hcE (δ := ‖w - PN w‖) (fun hΩ1 => by
        obtain ⟨p, hp, hpe⟩ := hwin k' hk' hΩ1
        have hwinc := (hfam k' hk').2.2.2 p hp PN (Pw k') (fun U => by rw [hpe]; exact hPN U)
          (fun U => by rw [hpe]; exact hP k' U)
        refine hwinc.trans (le_of_eq ?_)
        have := scalar_family_defect (stageSet b1wSt k) (e r) (fun i => star (β i)) w PN hPN
        rw [hβsum] at this
        exact congrArg (B ^ 2 * ·) this) (norm_nonneg _) (hΩw k' hk')
      ((hAf k' hk').trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEq hBζ)
        hsβ0))
    have hUqd := weighted_uq_le (Uq k') (Pw k') (hPn k') hCw hEpos.le (hUqn k' hk')
      (hΩq k' hk')
    exact weighted_rem_le hB hζ0 hζ1 hEpos.le hsβ0 hcE hCw
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEq hBζ) hsβ0) hAd hUqd
      (div_nonneg hAs0 hEpos.le) hAsE

end Frame

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # the transform of one constituent commutes with the transverse projection

The analogue of `realizes_gam` for `CommRep`: for a coefficient invariant along `e` in `z`,
the conjugated transform `R * star (letterGam ...)` of one constituent is realized by a map
commuting with the projection. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
  AVRegularity.CycleEvolution AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

theorem commRep_gam (e : Fin 2) (θ : Vec 2) (n N J : ℕ) (d : ℕ) (hd2 : 2 ≤ d)
    (hnd : n + d ≤ J) (hN1 : n + d ≤ N) (hN2 : d + 2 ≤ N) (pos : Bool) (slow : ℕ) (δ : ℝ)
    (X₀ : Vec 2) (r : ℝ) (coeff : DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec 2 → Vec 2)
    (jet : DerivativeWord2 (d - 1) → ℕ → ℕ → ℝ) (hjet0 : ∀ α s l, 0 ≤ jet α s l)
    (hfacts : ∀ α s, s ≤ slow → ∀ (ω : DerivativeWord2 s) (k' : Fin 2),
      ContDiff ℝ (J : ℕ∞) (tbTermCoef (coeff α r) s ω X₀ k') ∧
      AVenhance.IsZ2Periodic (tbTermCoef (coeff α r) s ω X₀ k') ∧
      ∀ l ≤ J, ∀ z, ‖iteratedFDeriv ℝ l (tbTermCoef (coeff α r) s ω X₀ k') z‖ ≤ jet α s l)
    (htr : ∀ (α : DerivativeWord2 (d - 1)) (X z : Vec 2) (t : ℝ),
      coeff α r X (z + t • basisVec e) = coeff α r X z)
    (Rcv : ℝ) (β₀ : ℕ × ℕ) (k : Fin 2) (β' : ℕ × ℕ) (pre : Bool) :
    CommRep e N n (fun f z => (Rcv : ℂ) * star (letterGam θ pos slow δ X₀ r d coeff β₀ k β'
        (variantFun pre (-θ) k (fun y => star (f y))) z)) := by
  classical
  have hd1 : d - 1 + 1 = d := by omega
  have unit : ∀ (α : DerivativeWord2 (d - 1)) (s : ℕ), s ≤ slow → ∀ (ω : DerivativeWord2 s)
      (a : ℕ × ℕ), a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ Finset.range ((wordCount α).2 + 1) →
      CommRep e N n (fun f z => ((gamK Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω)
          a β' : ℝ) : ℂ) * fibreCovPow θ ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
          (fun y => (tbTermCoef (coeff α r) s ω X₀ k y : ℂ) * variantFun pre θ k f y) z) := by
    intro α s hs ω a ha
    have hwc := wordCount_sum α
    have hpq : ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2) ≤ d - 1 := by omega
    obtain ⟨hc, hp, hj⟩ := hfacts α s hs ω k
    have hc' : ContDiff ℝ ((n + ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2) : ℕ) : ℕ∞)
        (tbTermCoef (coeff α r) s ω X₀ k) := hc.of_le (by exact_mod_cast (by omega))
    have hP : ∀ l ≤ n + ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2), ∀ x,
        ‖iteratedFDeriv ℝ l (tbTermCoef (coeff α r) s ω X₀ k) x‖ ≤
          ∑ l ∈ Finset.range (J + 1), jet α s l := by
      intro l hl x
      refine (hj l (by omega) x).trans ?_
      exact Finset.single_le_sum (f := fun l => jet α s l) (fun l _ => hjet0 α s l)
        (Finset.mem_range.2 (by omega))
    have ht : ∀ (z : Vec 2) (t : ℝ), tbTermCoef (coeff α r) s ω X₀ k (z + t • basisVec e) =
        tbTermCoef (coeff α r) s ω X₀ k z := by
      intro z t
      unfold tbTermCoef
      simp only [htr α]
    cases pre
    · have := commRep_unit0 e θ n N ((wordCount α).1 - a.1) ((wordCount α).2 - a.2)
        (by omega) (by omega) hc' hp hP ht
        (gamK Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β')
      simpa [variantFun] using this
    · have := commRep_unit1 e θ n N ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) k
        (by omega) (by omega) hc' hp hP ht
        (gamK Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β')
      simpa [variantFun] using this
  have hsum : CommRep e N n (fun f z => ∑ α : DerivativeWord2 (d - 1),
      ∑ s ∈ Finset.Icc (if pos then 1 else 0) slow, ∑ ω : DerivativeWord2 s,
        ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ Finset.range ((wordCount α).2 + 1),
          ((gamK Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β' : ℝ) : ℂ) *
            fibreCovPow θ ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
              (fun y => (tbTermCoef (coeff α r) s ω X₀ k y : ℂ) * variantFun pre θ k f y) z) :=
    CommRep.finset_sum (e := e) (N := N) (n := n) Finset.univ (fun α _ =>
      CommRep.finset_sum _ (fun s hs =>
        CommRep.finset_sum _ (fun ω _ =>
          CommRep.finset_sum _ (fun a ha =>
            unit α s (Finset.mem_Icc.1 hs).2 ω a ha))))
  refine hsum.congr (fun ψ => ?_)
  funext z
  have hcd : ContDiff ℝ (d : ℕ∞) (torusHigherClassicalValue N ψ) :=
    torusHigherClassicalValue_contDiff N d (by omega) ψ
  have hdiff : Differentiable ℝ (torusHigherClassicalValue N ψ) :=
    (hcd.of_le (by exact_mod_cast (by omega : 1 ≤ d))).differentiable one_ne_zero
  have hfv : ContDiff ℝ ((d - 1 : ℕ) : ℕ∞) (variantFun pre θ k (torusHigherClassicalValue N ψ)) :=
    contDiff_variantFun pre θ k (m := d - 1) (by rw [hd1]; exact hcd)
  rw [variantFun_star pre θ k hdiff]
  unfold letterGam
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hwc := wordCount_sum α
  have hJd : d - 1 ≤ J := by omega
  have key := star_gam_alpha θ d s δ (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) β'
    (tbTermCoef (coeff α r) s ω X₀ k) (variantFun pre θ k (torusHigherClassicalValue N ψ)) Rcv
    (fun a ha => by
      obtain ⟨hc, -, -⟩ := hfacts α s (Finset.mem_Icc.1 hs).2 ω k
      have hle : (wordCount α).1 - a.1 + ((wordCount α).2 - a.2) ≤ J := by omega
      have hle2 : (wordCount α).1 - a.1 + ((wordCount α).2 - a.2) ≤ d - 1 := by omega
      exact contDiff_real_mul_complex (m := (wordCount α).1 - a.1 + ((wordCount α).2 - a.2))
        (hc.of_le (by exact_mod_cast hle)) (hfv.of_le (by exact_mod_cast hle2))) z
  exact key.symm

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # the block entries of a letter commute with the transverse projection

Every entry `(b, b')` of the conjugated letter transform `letterGfam` of the components `x, x'` and
the moments `β, β'` is realized by a map commuting with the transverse projection, when every
constituent coefficient is invariant along `e` in `z` at the time `r`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
  AVRegularity.CycleEvolution AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D Nw : ℕ}

/-- **One constituent of one variant** commutes with the projection. -/
theorem commRep_term (e : Fin 2) (π : ι → ℝ) (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Icc a b ×ˢ Set.univ) J H) (r : ℝ) (hr : r ∈ Icc a b)
    (hg : LetterGood L (Icc a b) J r) (δ : ℝ) (θ : Vec 2) (X₀ : Vec 2)
    (n N Dmax : ℕ) (hord : L.order ≤ Dmax) (hJ : n + Dmax ≤ J) (hN1 : n + L.order ≤ N)
    (hN2 : Dmax + 3 ≤ N) (x x' : ι) (β' : ℕ × ℕ) (w : ℝ × (ℕ × ℕ) × Fin 2 × Bool) (R : ℝ)
    (d : ℕ) (hd : d ∈ Finset.Icc 2 D) (γ : Constituent d (h x') (h x))
    (hγ : γ ∈ L.edge x x' ⟨d, hd⟩)
    (htr : ∀ α (X z : Vec 2) (t : ℝ), γ.coeff α r X (z + t • basisVec e) = γ.coeff α r X z)
    (b₁ : Fin (Module.finrank ℝ (h x))) (b₂ : Fin (Module.finrank ℝ (h x'))) :
    CommRep e N n (fun f z =>
      ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b₁ b₂ : ℝ) : ℂ) *
        (((R * w.1 : ℝ) : ℂ) * star (letterGam θ L.positive L.slow δ X₀ r d γ.coeff w.2.1
          w.2.2.1 β' (variantFun w.2.2.2 (-θ) w.2.2.1 (fun y => star (f y))) z))) := by
  by_cases hm : γ.map = 0
  · refine (CommRep.zero (e := e) (N := N) (n := n)).congr fun ψ => funext fun z => ?_
    simp [letterMat, hm]
  · obtain ⟨k, hk⟩ := List.mem_iff_get.1 hγ
    subst hk
    have hdle : d ≤ L.order := by
      by_contra hlt
      have := hL.edge_order x x' ⟨d, hd⟩ (by simpa using not_le.1 hlt)
      have hk' := k.2
      simp [this] at hk'
    have hd2 : 2 ≤ d := (Finset.mem_Icc.1 hd).1
    let jet : DerivativeWord2 (d - 1) → ℕ → ℕ → ℝ := fun α s q =>
      (jetSupOn (Icc a b ×ˢ Set.univ) s q (((L.edge x x' ⟨d, hd⟩).get k).coeff α)).toReal
    have hjet0 : ∀ α s q, 0 ≤ jet α s q := fun _ _ _ => ENNReal.toReal_nonneg
    have hfacts : ∀ α s, s ≤ L.slow → ∀ (ω : DerivativeWord2 s) (k' : Fin 2),
        ContDiff ℝ (J : ℕ∞) (tbTermCoef ((((L.edge x x' ⟨d, hd⟩).get k)).coeff α r) s ω X₀ k') ∧
        AVenhance.IsZ2Periodic
          (tbTermCoef ((((L.edge x x' ⟨d, hd⟩).get k)).coeff α r) s ω X₀ k') ∧
        ∀ q ≤ J, ∀ z, ‖iteratedFDeriv ℝ q
          (tbTermCoef ((((L.edge x x' ⟨d, hd⟩).get k)).coeff α r) s ω X₀ k') z‖ ≤ jet α s q :=
      fun α s hs ω k' => letter_term_facts π L a b J H hL r hr hg x x' ⟨d, hd⟩ k hm α s hs
        ω X₀ k'
    have hreal := commRep_gam e θ n N J d hd2 (by omega) (by omega) (by omega)
      L.positive L.slow δ X₀ r ((L.edge x x' ⟨d, hd⟩).get k).coeff jet hjet0 hfacts htr
      (R * w.1) w.2.1 w.2.2.1 β' w.2.2.2
    exact hreal.smul (letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x'))
      ((L.edge x x' ⟨d, hd⟩).get k).map b₁ b₂)

/-- **One variant** commutes with the projection. -/
theorem commRep_variant (e : Fin 2) (π : ι → ℝ) (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Icc a b ×ˢ Set.univ) J H) (r : ℝ) (hr : r ∈ Icc a b)
    (hg : LetterGood L (Icc a b) J r) (δ : ℝ) (θ : Vec 2) (X₀ : Vec 2) (A : Finset ℕ)
    (n N Dmax : ℕ) (hord : L.order ≤ Dmax) (hJ : n + Dmax ≤ J) (hN1 : n + L.order ≤ N)
    (hN2 : Dmax + 3 ≤ N)
    (htr : ∀ x y (o : Finset.Icc 2 D), ∀ γ ∈ L.edge x y o, ∀ α (X z : Vec 2) (t : ℝ),
      γ.coeff α r X (z + t • basisVec e) = γ.coeff α r X z)
    (x x' : ι) (β' : ℕ × ℕ) (w : ℝ × (ℕ × ℕ) × Fin 2 × Bool) (R : ℝ)
    (b₁ : Fin (Module.finrank ℝ (h x))) (b₂ : Fin (Module.finrank ℝ (h x'))) :
    CommRep e N n (fun f z => ∑ d ∈ A, if hd : d ∈ Finset.Icc 2 D then
      ((L.edge x x' ⟨d, hd⟩).map fun γ =>
        ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b₁ b₂ : ℝ) : ℂ) *
          (((R * w.1 : ℝ) : ℂ) * star (letterGam θ L.positive L.slow δ X₀ r d γ.coeff w.2.1
            w.2.2.1 β' (variantFun w.2.2.2 (-θ) w.2.2.1 (fun y => star (f y))) z))).sum
      else 0) := by
  classical
  refine CommRep.finset_sum (e := e) (N := N) (n := n) A fun d _ => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, dite_true]
    exact CommRep.list_sum (e := e) (N := N) (n := n) (L.edge x x' ⟨d, hd⟩) fun γ hγ =>
      commRep_term e π L a b J H hL r hr hg δ θ X₀ n N Dmax hord hJ hN1 hN2 x x' β' w R d hd γ hγ
        (htr x x' ⟨d, hd⟩ γ hγ) b₁ b₂
  · simp only [hd, dite_false]
    exact CommRep.zero

/-- **The block entries commute with the projection.** -/
theorem commRep_letterGfam (e : Fin 2) (π : ι → ℝ) (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Icc a b ×ˢ Set.univ) J H) (r : ℝ) (hr : r ∈ Icc a b)
    (hg : LetterGood L (Icc a b) J r) (δ : ℝ) (θ : Vec 2) (X₀ : Vec 2) (A : Finset ℕ)
    (n N Dmax : ℕ) (hord : L.order ≤ Dmax) (hJ : n + Dmax ≤ J) (hN1 : n + L.order ≤ N)
    (hN2 : Dmax + 3 ≤ N)
    (htr : ∀ x y (o : Finset.Icc 2 D), ∀ γ ∈ L.edge x y o, ∀ α (X z : Vec 2) (t : ℝ),
      γ.coeff α r X (z + t • basisVec e) = γ.coeff α r X z)
    (x x' : ι) (β β' : ℕ × ℕ) (R : ℝ) (b₁ : Fin (Module.finrank ℝ (h x)))
    (b₂ : Fin (Module.finrank ℝ (h x'))) :
    CommRep e N n (letterGfam θ L A δ X₀ r x x' β β' R b₁ b₂) := by
  have := CommRep.list_sum (e := e) (N := N) (n := n) (letterVars β)
    (fun w _ => commRep_variant e π L a b J H hL r hr hg δ θ X₀ A n N Dmax hord hJ hN1 hN2 htr
      x x' β' w R b₁ b₂)
  exact this

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # B1.W sharp pass (weighted norm): the H4 decomposition at one time

Along an adjoint curve the tests at time `r` are general: `ψ_i ∈ H^N` (the curve values), of
`H^N` size `≤ Y` and, where `Ω_{k'}(r) > 1`, of weighted defect
`Ω_{k'}(r)‖ψ − P_N ψ‖ ≤ Y`. The stage representation with the sharp families
(`b1w_sharp_repr_general_at`) is split exactly along the slow test (`b1w_weighted_blocks`). The
bounds:
* coefficients: `≤ ΘζY/|E|`, by the slow–fast pairing of the sharp stage-transform families;
* weighted remainders: `≤ ΘY`;
* the identity is exact (`b1w_weighted_H4_at`).

`Θ = b1wWeightedΘ` is the constant of the weighted H3s. In B1.W, `Y = C_f e^{-π²(T−r)/8}` comes
from the weighted sharp decay at the level `Λ^{k'+1}` (`ν_{k'}`), whose split gives `‖ψ − P_N ψ‖ ≤ 2‖V_N‖`. -/

universe u v

/-- The remainder algebra of the weighted H4. -/
theorem weighted_H4_rem_le {B ζ En Y cE Cw Af ΩAd Uqd As : ℝ} (hB : 0 ≤ B) (hζ1 : ζ ≤ 1)
    (hEn : 0 < En) (hY : 0 ≤ Y) (hcE : 0 ≤ cE) (hCw : 0 ≤ Cw)
    (hAf : Af ≤ B * Y) (hAd : ΩAd ≤ B * 1 * Y * 1 * (1 + 2 * 1))
    (hUq : Uqd ≤ (3 * Cw + 1) * En) (hAs0 : 0 ≤ As) (hAs : As ≤ B * ζ * Y / En) :
    Af + ΩAd + Uqd * As ≤ b1wWeightedΘ B cE Cw * Y := by
  have hAs' : As ≤ B * Y / En := hAs.trans (div_le_div_of_nonneg_right
    (by nlinarith [mul_nonneg hB hY]) hEn.le)
  have h3 : Uqd * As ≤ (3 * Cw + 1) * En * (B * Y / En) :=
    mul_le_mul hUq hAs' hAs0 (by positivity)
  have e3 : (3 * Cw + 1) * En * (B * Y / En) = (3 * Cw + 1) * (B * Y) := by
    field_simp
  have hBY : 0 ≤ B * Y := mul_nonneg hB hY
  have hsum : Af + ΩAd + Uqd * As ≤ (5 + 3 * Cw) * (B * Y) := by nlinarith
  have h5 : 0 ≤ (5 + 3 * Cw) * (B * Y) := mul_nonneg (by linarith) hBY
  calc Af + ΩAd + Uqd * As ≤ (5 + 3 * Cw) * (B * Y) := hsum
    _ ≤ (1 + cE) * ((5 + 3 * Cw) * (B * Y)) := le_mul_of_one_le_left h5 (by linarith)
    _ = b1wWeightedΘ B cE Cw * Y := by simp only [b1wWeightedΘ]; ring

theorem le_b1wWeightedΘ {B cE Cw : ℝ} (hB : 0 ≤ B) (hcE : 0 ≤ cE) (hCw : 0 ≤ Cw) :
    B ≤ b1wWeightedΘ B cE Cw := by
  have h1 : (1 : ℝ) ≤ (1 + cE) * (5 + 3 * Cw) := by nlinarith [mul_nonneg hcE hCw]
  calc B = B * 1 := (mul_one B).symm
    _ ≤ B * ((1 + cE) * (5 + 3 * Cw)) := mul_le_mul_of_nonneg_left h1 hB
    _ = b1wWeightedΘ B cE Cw := by simp only [b1wWeightedΘ]; ring

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The weighted H4 decomposition at one time.** -/
theorem b1w_weighted_H4_at {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (k : ℕ) (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (s : ℕ → ℕ) (n N : ℕ) (hN : n + 3 ≤ N)
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
    (B M₀ : ℝ)
    (hprov : ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ, ∀ k' < k,
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
        B1WSharpFamily F θ r k k' N (s k') ψ Φ B M₀)
    (hB : 0 ≤ B) (tr : ℝ → ComplexCellL2) (Ω : ℕ → ℝ → ℝ) (e : ℝ → Fin 2)
    (hΩ0 : ∀ k', 0 ≤ Ω k' r)
    (htr : ‖tr r‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ))
    (q : ComplexCellL2) (E : ℂ) (hE : cellComplexPair (tr r + cellConstantCLM 1) q = E)
    (hE0 : E ≠ 0) (cE Cw : ℝ) (hcE : 0 ≤ cE) (hCw : 0 ≤ Cw)
    (Uq : ∀ k', TorusHk (s k') ℂ) (hUq : ∀ k' < k, torusHkValueCLM (Uq k') = q)
    (hUqn : ∀ k' < k, ‖Uq k'‖ ≤ Cw * ‖E‖)
    (PN : TorusHk N ℂ →L[ℝ] TorusHk N ℂ)
    (hPN : ∀ U, torusHkValueCLM (PN U) = cellTransverseProjection (e r) (torusHkValueCLM U))
    (Pw : ∀ k', TorusHk (s k') ℂ →L[ℝ] TorusHk (s k') ℂ)
    (hP : ∀ k' U, torusHkValueCLM (Pw k' U) =
      cellTransverseProjection (e r) (torusHkValueCLM U))
    (hPn : ∀ k' U, ‖Pw k' U‖ ≤ ‖U‖)
    (hwin : ∀ k' < k, 1 < Ω k' r → ∃ p, IsLeastWindow F.reg p r ∧ F.reg.orient p = e r)
    (hΩq : ∀ k' < k, 1 < Ω k' r → Ω k' r * ‖Uq k' - Pw k' (Uq k')‖ ≤ ‖E‖)
    (z : B1WIndex ι h Nw m Ks → TorusHk 1 ℂ) (ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ)
    (hzψ : ∀ i, torusHkValueCLM (z i) = torusHkValueCLM (ψ i)) (Y : ℝ) (hY0 : 0 ≤ Y)
    (hY : Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2) ≤ Y)
    (hYd : ∀ k' < k, 1 < Ω k' r →
      Ω k' r * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i - PN (ψ i)‖ ^ 2) ≤ Y) :
    ∃ (κ : B1WIndex ι h Nw m Ks → ℂ) (φ : B1WIndex ι h Nw m Ks → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet b1wSt k', b1wAdm s tr k' r (φ i')) ∧
      (∀ k' < k, stageNorm b1wSt k' κ ≤ b1wWeightedΘ B cE Cw *
        min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) * Y / ‖E‖) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', b1wNuW s Ω e k' r (φ i') ^ 2) ≤
        b1wWeightedΘ B cE Cw * Y) ∧
      ∑ i ∈ stageSet b1wSt k, cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) (z i) =
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k',
          (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i')) := by
  classical
  obtain ⟨UΦ, Φall, hUΦval, hfam, hrep⟩ := b1w_sharp_repr_general_at F θ r k hπ hϖ s n N hN W S
    Fl hS hF hExp hearly hW B M₀ hprov z ψ hzψ
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = fibreNorm (planeFibreFrequency F.η θ) := ⟨_, rfl⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ, ζ = min 1 (x + (Real.sqrt F.S)⁻¹) := ⟨_, rfl⟩
  rw [← hx] at htr
  rw [← hx, ← hζ]
  have hEpos : 0 < ‖E‖ := norm_pos_iff.2 hE0
  have hg : cellComplexPair (tr r + cellConstantCLM 1) q ≠ 0 := by rw [hE]; exact hE0
  have hx0 : 0 ≤ x := hx ▸ fibreNorm_nonneg _
  have hζ0 : 0 ≤ ζ := hζ ▸ le_min zero_le_one (add_nonneg hx0 (inv_nonneg.2 (Real.sqrt_nonneg _)))
  have hζ1 : ζ ≤ 1 := hζ ▸ min_le_left _ _
  have hS0 := Real.sqrt_nonneg (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)
  -- the aggregates
  have hAs : ∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k',
      ‖cellComplexPair (tr r + cellConstantCLM 1) (Φall i')‖ ^ 2) ≤ B * ζ * Y := by
    intro k' hk'
    have hf := (hfam k' hk').2.2.1
    rw [← hx, ← hζ] at hf
    rw [Finset.sum_congr rfl fun i' hi' => by rw [← hUΦval k' hk' i' hi']]
    refine (Real.sqrt_le_sqrt (hf.1 (tr r) htr)).trans ?_
    rw [show B ^ 2 * ζ ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2 =
      (B * ζ) ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2 by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (mul_nonneg hB hζ0)]
    exact mul_le_mul_of_nonneg_left hY (mul_nonneg hB hζ0)
  have hAf : ∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', ‖UΦ k' i'‖ ^ 2) ≤ B * Y := by
    intro k' hk'
    refine (Real.sqrt_le_sqrt (hfam k' hk').2.1).trans ?_
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB]
    exact mul_le_mul_of_nonneg_left hY hB
  -- the weighted blocks
  obtain ⟨κ, φ, hadm, hκb, hνb, hid⟩ := b1w_weighted_blocks s Ω e tr r hΩ0 b1wSt k W q _ Φall
    hg Uq hUq Pw hP hPn (fun k' => ‖Uq k' - Pw k' (Uq k')‖) (fun _ => norm_nonneg _)
    (fun _ _ => le_rfl) UΦ hUΦval (fun _ => B * ζ * Y) (fun _ => B * Y)
    (fun k' => Real.sqrt (∑ i' ∈ stageSet b1wSt k', ‖UΦ k' i' - Pw k' (UΦ k' i')‖ ^ 2))
    hAs hAf (fun _ _ => le_rfl) hrep
  rw [hE] at hκb hνb
  have hBΘ : B ≤ b1wWeightedΘ B cE Cw := le_b1wWeightedΘ hB hcE hCw
  refine ⟨κ, φ, hadm, fun k' hk' => (hκb k' hk').trans ?_, fun k' hk' => ?_, hid⟩
  · refine div_le_div_of_nonneg_right ?_ hEpos.le
    calc B * ζ * Y = B * (ζ * Y) := by ring
      _ ≤ b1wWeightedΘ B cE Cw * (ζ * Y) :=
          mul_le_mul_of_nonneg_right hBΘ (mul_nonneg hζ0 hY0)
      _ = b1wWeightedΘ B cE Cw * ζ * Y := by ring
  · refine (hνb k' hk').trans ?_
    have hΩk := hΩ0 k'
    have hAd := weighted_stage_defect (stageSet b1wSt k') (UΦ k') (Pw k') (hPn k') hΩk hB
      zero_le_one hY0 zero_le_one zero_le_one
      (δ := Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i - PN (ψ i)‖ ^ 2)) (fun hΩ1 => by
        obtain ⟨p, hp, hpe⟩ := hwin k' hk' hΩ1
        have hwinc := (hfam k' hk').2.2.2 p hp PN (Pw k') (fun U => by rw [hpe]; exact hPN U)
          (fun U => by rw [hpe]; exact hP k' U)
        refine hwinc.trans (le_of_eq ?_)
        rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), one_pow, mul_one])
      (Real.sqrt_nonneg _) (fun hΩ1 => by rw [one_mul]; exact hYd k' hk' hΩ1)
      ((hAf k' hk').trans (le_of_eq (by ring)))
    have hUqd := weighted_uq_le (Uq k') (Pw k') (hPn k') hCw hEpos.le (hUqn k' hk')
      (hΩq k' hk')
    exact weighted_H4_rem_le hB hζ1 hEpos hY0 hcE hCw le_rfl hAd hUqd
      (div_nonneg (mul_nonneg (mul_nonneg hB hζ0) hY0) hEpos.le) le_rfl

end Frame

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # the letter operators commute with the transverse projection in the least window

`SharpLetterCommFact`: any operator family with the value formula of the conjugated stage letter
transform equals the explicit block entry of `commRep_letterGfam` (the value map of `H^n` is
injective), so it commutes with the projection once the constituent coefficients are invariant
along the orientation at the time `r`. In the least window that is `htrans` on the pulse
`[lo_p, hi_p]` and `hquiet` on the quiet half buffer. -/

universe u v

open Classical in
/-- **The commutation fact.** -/
theorem sharpLetterComm : SharpLetterCommFact.{u, v} := by
  intro K Nw D m d Ks pos ρ n g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  have hgood : ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)),
      ∀ l, LetterGood (F.letters l) (Icc F.a F.b) F.J r := by
    have h1 : ∀ᵐ r ∂(volume : Measure ℝ), ∀ l, r ∈ Icc F.a F.b →
        LetterGood (F.letters l) (Icc F.a F.b) F.J r :=
      ae_all_iff.2 fun l => letterGood_ae F.π F.piece.hπ (F.letters l) (Icc F.a F.b) F.J F.H
        (F.piece.hlet l)
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h1] with r hr hrI l using hr l hrI
  filter_upwards [hgood, ae_restrict_mem measurableSet_Icc] with r hg hr
  intro l N hN1 hN2 T hTv p hp PN Pn hPN hPn i i' hi hi' φ
  have hord : (F.letters l).order ≤ Finset.univ.sup d := by
    rw [(hlet l).1]; exact Finset.le_sup (f := d) (Finset.mem_univ l)
  have hN1' : n + (F.letters l).order ≤ N := by rw [(hlet l).1]; exact hN1
  have htr : ∀ x y (o : Finset.Icc 2 D), ∀ γ ∈ (F.letters l).edge x y o, ∀ α (X z : Vec 2)
      (t : ℝ), γ.coeff α r X (z + t • basisVec (F.reg.orient p)) = γ.coeff α r X z := by
    intro x y o γ hγ α X z t
    rcases le_or_gt r (F.reg.hi p) with hle | hlt
    · exact F.piece.htrans l p x y o γ hγ α r ⟨hp.1.1, hle⟩ X z t
    · have hq : r ∈ F.reg.quiet := (F.pkg.buffer_quiet p).2
        ⟨hlt, by linarith [hp.1.2, F.pkg.buffer_nonneg]⟩
      exact (F.piece.hquiet l).2 x y o γ hγ α r hq X _ _
  obtain ⟨A, hAv, hAc⟩ := commRep_letterGfam (F.reg.orient p) F.π (F.letters l) F.a F.b F.J F.H
    (F.piece.hlet l) r hr (hg l) (F.ϖ * F.ηg) θ F.X₀
    (admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D (l.succ, i.2.1)
      (l.castSucc, i'.2.1)) n N (Finset.univ.sup d) hord hJ hN1' hN2 htr i.2.1 i'.2.1
    (b1wMom i) (b1wMom i')
    (letterRatioReal F.π F.ϖ F.ηg F.letters l i.2.1 i'.2.1 (b1wMom i) (b1wMom i'))
    i.2.2.2 i'.2.2.2
  have hTA : ∀ ψ : TorusHk N ℂ, T i i' ψ = A ψ := fun ψ => by
    apply TorusHk.ext_value
    change torusHkValueCLM (T i i' ψ) = torusHkValueCLM (A ψ)
    apply Lp.ext
    filter_upwards [hTv i i' hi hi' ψ, hAv ψ] with z h1 h2
    rw [h1, h2, b1wScaleRatio_letter F.π F.ϖ F.ηg F.letters l i i' hi hi',
      ratio_star_letterTransform F θ l i i' hi hi' r _ z]
  have hPn' : ∀ U : TorusHk n ℂ, Pn U = commProj (F.reg.orient p) n U := fun U => by
    apply TorusHk.ext_value
    change torusHkValueCLM (Pn U) = torusHkValueCLM (commProj (F.reg.orient p) n U)
    rw [hPn, commProj_value]
  have hPN' : ∀ U : TorusHk N ℂ, PN U = commProj (F.reg.orient p) N U := fun U => by
    apply TorusHk.ext_value
    change torusHkValueCLM (PN U) = torusHkValueCLM (commProj (F.reg.orient p) N U)
    rw [hPN, commProj_value]
  rw [hPn', hPN', hTA, hTA, hAc]

end AVRegularity.CycleWords.Assembly
end
end
