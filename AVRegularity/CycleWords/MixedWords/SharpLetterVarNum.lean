-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.SharpLetterHelperUnits
import AVRegularity.CycleWords.MixedWords.ConstituentTransposeStep

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # closure of the unit bundle `RQ` and its block lift

`RQ` is closed under zero, monotonicity, congruence, sums.  `BRQ` is the block version
(a family of operators `T b b'` with four block bounds); `brq_of_rq` lifts an `RQ` through the
letter matrix `letterMat`, and `BRQ` is closed under the same operations plus lists. -/

section
section RQClosure

variable {L n Nmin : ℕ} {G G' : (Vec 2 → ℂ) → Vec 2 → ℂ} {B1 B2 B3 B4 C1 C2 C3 C4 : ℝ}

theorem rq_zero : RQ L n Nmin (fun _ _ => 0) 0 0 0 0 :=
  ⟨0, fun N hLN hN ψ => by
    rw [zero_apply, map_zero]; exact Lp.coeFn_zero _ _ _,
    fun ψ => by simp, fun ψ => by simp, fun z => by simp, fun z => by simp⟩

theorem rq_mono (h : RQ L n Nmin G B1 B2 B3 B4) (h1 : B1 ≤ C1) (h2 : B2 ≤ C2) (h3 : B3 ≤ C3)
    (h4 : B4 ≤ C4) : RQ L n Nmin G C1 C2 C3 C4 := by
  obtain ⟨A, hv, b1, b2, b3, b4⟩ := h
  exact ⟨A, hv, fun ψ => (b1 ψ).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)),
    fun ψ => (b2 ψ).trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)),
    fun z => (b3 z).trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _)),
    fun z => (b4 z).trans (mul_le_mul_of_nonneg_right h4 (norm_nonneg _))⟩

theorem rq_congr (h : RQ L n Nmin G B1 B2 B3 B4)
    (hG : ∀ (N : ℕ), L ≤ N → Nmin ≤ N → ∀ ψ : TorusHk N ℂ,
      G (torusHigherClassicalValue N ψ) = G' (torusHigherClassicalValue N ψ)) :
    RQ L n Nmin G' B1 B2 B3 B4 := by
  obtain ⟨A, hv, b⟩ := h
  exact ⟨A, fun N hLN hN ψ => by rw [← hG N hLN hN ψ]; exact hv N hLN hN ψ, b⟩

theorem rq_add (h : RQ L n Nmin G B1 B2 B3 B4) (h' : RQ L n Nmin G' C1 C2 C3 C4) :
    RQ L n Nmin (fun f z => G f z + G' f z) (B1 + C1) (B2 + C2) (B3 + C3) (B4 + C4) := by
  obtain ⟨A, hv, b1, b2, b3, b4⟩ := h
  obtain ⟨A', hv', c1, c2, c3, c4⟩ := h'
  refine ⟨A + A', fun N hLN hN ψ => ?_, fun ψ => ?_, fun ψ => ?_, fun z => ?_, fun z => ?_⟩
  · rw [add_apply, map_add]
    filter_upwards [Lp.coeFn_add (torusHkValueCLM (A (truncateTorusHk hLN ψ)))
      (torusHkValueCLM (A' (truncateTorusHk hLN ψ))), hv N hLN hN ψ, hv' N hLN hN ψ]
      with z h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
  · rw [add_apply]
    exact (norm_add_le _ _).trans (by linarith [b1 ψ, c1 ψ])
  · rw [add_apply, map_add]
    exact (norm_add_le _ _).trans (by linarith [b2 ψ, c2 ψ])
  · rw [add_apply]
    exact (norm_add_le _ _).trans (by linarith [b3 z, c3 z])
  · rw [add_apply, map_add]
    exact (norm_add_le _ _).trans (by linarith [b4 z, c4 z])

theorem rq_finset_sum {κ : Type*} (s : Finset κ) {G : κ → (Vec 2 → ℂ) → Vec 2 → ℂ}
    {B1 B2 B3 B4 : κ → ℝ} (h : ∀ j ∈ s, RQ L n Nmin (G j) (B1 j) (B2 j) (B3 j) (B4 j)) :
    RQ L n Nmin (fun f z => ∑ j ∈ s, G j f z) (∑ j ∈ s, B1 j) (∑ j ∈ s, B2 j) (∑ j ∈ s, B3 j)
      (∑ j ∈ s, B4 j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rq_zero (L := L) (n := n) (Nmin := Nmin))
  | insert a s ha ih =>
    have := rq_add (h a (Finset.mem_insert_self a s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert ha] using this

end RQClosure

section BRQ

variable {m₁ m₂ : ℕ}

/-- The block version of `RQ`: a family of operators with value formulas and four block bounds. -/
def BRQ (L n Nmin : ℕ) (G : Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ) (c1 c2 c3 c4 : ℝ) : Prop :=
  ∃ T : Fin m₁ → Fin m₂ → TorusHk L ℂ →L[ℝ] TorusHk n ℂ,
    (∀ (N : ℕ) (hLN : L ≤ N), Nmin ≤ N → ∀ b b' (ψ : TorusHk N ℂ),
      (torusHkValueCLM (T b b' (truncateTorusHk hLN ψ)) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] G b b' (torusHigherClassicalValue N ψ)) ∧
    BlockBound c1 T ∧ BlockBound c2 (fun b b' => (slMeanOp n).comp (T b b')) ∧
    BlockBound c3 (fun b b' => (T b b').comp (slConstCLM L)) ∧
    BlockBound c4 (fun b b' => (slMeanOp n).comp ((T b b').comp (slConstCLM L)))

variable {L n Nmin : ℕ} {G G' : Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ} {c1 c2 c3 c4 d1 d2 d3 d4 : ℝ}

theorem brq_zero : BRQ (m₁ := m₁) (m₂ := m₂) L n Nmin (fun _ _ _ _ => 0) 0 0 0 0 :=
  ⟨fun _ _ => 0, fun N hLN hN b b' ψ => by
    rw [zero_apply, map_zero]; exact Lp.coeFn_zero _ _ _,
    BlockBound.zero, by simpa using (BlockBound.zero (m₁ := m₁) (m₂ := m₂) (X := TorusHk L ℂ) (Y := ℂ)),
    BlockBound.zero, by simpa using (BlockBound.zero (m₁ := m₁) (m₂ := m₂) (X := ℂ) (Y := ℂ))⟩

theorem brq_mono (h : BRQ L n Nmin G c1 c2 c3 c4) (h1 : c1 ≤ d1) (h2 : c2 ≤ d2) (h3 : c3 ≤ d3)
    (h4 : c4 ≤ d4) : BRQ L n Nmin G d1 d2 d3 d4 := by
  obtain ⟨T, hv, b1, b2, b3, b4⟩ := h
  exact ⟨T, hv, b1.mono h1, b2.mono h2, b3.mono h3, b4.mono h4⟩

theorem brq_congr (h : BRQ L n Nmin G c1 c2 c3 c4)
    (hG : ∀ (N : ℕ), L ≤ N → Nmin ≤ N → ∀ b b' (ψ : TorusHk N ℂ),
      G b b' (torusHigherClassicalValue N ψ) = G' b b' (torusHigherClassicalValue N ψ)) :
    BRQ L n Nmin G' c1 c2 c3 c4 := by
  obtain ⟨T, hv, b⟩ := h
  exact ⟨T, fun N hLN hN b b' ψ => by rw [← hG N hLN hN b b' ψ]; exact hv N hLN hN b b' ψ, b⟩

theorem brq_add (h : BRQ L n Nmin G c1 c2 c3 c4) (h' : BRQ L n Nmin G' d1 d2 d3 d4) :
    BRQ L n Nmin (fun b b' f z => G b b' f z + G' b b' f z) (c1 + d1) (c2 + d2) (c3 + d3)
      (c4 + d4) := by
  obtain ⟨T, hv, b1, b2, b3, b4⟩ := h
  obtain ⟨T', hv', e1, e2, e3, e4⟩ := h'
  refine ⟨fun b b' => T b b' + T' b b', fun N hLN hN b b' ψ => ?_, b1.add e1, ?_, ?_, ?_⟩
  · rw [add_apply, map_add]
    filter_upwards [Lp.coeFn_add (torusHkValueCLM (T b b' (truncateTorusHk hLN ψ)))
      (torusHkValueCLM (T' b b' (truncateTorusHk hLN ψ))), hv N hLN hN b b' ψ,
      hv' N hLN hN b b' ψ] with z h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
  · simpa only [ContinuousLinearMap.comp_add] using b2.add e2
  · simpa only [ContinuousLinearMap.add_comp] using b3.add e3
  · simpa only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add] using b4.add e4

theorem brq_finset_sum {κ : Type*} (s : Finset κ)
    {G : κ → Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ} {c1 c2 c3 c4 : κ → ℝ}
    (h : ∀ j ∈ s, BRQ L n Nmin (G j) (c1 j) (c2 j) (c3 j) (c4 j)) :
    BRQ L n Nmin (fun b b' f z => ∑ j ∈ s, G j b b' f z) (∑ j ∈ s, c1 j) (∑ j ∈ s, c2 j)
      (∑ j ∈ s, c3 j) (∑ j ∈ s, c4 j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (brq_zero (m₁ := m₁) (m₂ := m₂) (L := L) (n := n) (Nmin := Nmin))
  | insert a s ha ih =>
    have := brq_add (h a (Finset.mem_insert_self a s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert ha] using this

theorem brq_list_sum {κ : Type*} (l : List κ)
    {G : κ → Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ} {c1 c2 c3 c4 : κ → ℝ}
    (h : ∀ j ∈ l, BRQ L n Nmin (G j) (c1 j) (c2 j) (c3 j) (c4 j)) :
    BRQ L n Nmin (fun b b' f z => (l.map fun j => G j b b' f z).sum) (l.map c1).sum
      (l.map c2).sum (l.map c3).sum (l.map c4).sum := by
  induction l with
  | nil => simpa using (brq_zero (m₁ := m₁) (m₂ := m₂) (L := L) (n := n) (Nmin := Nmin))
  | cons a l ih =>
    have := brq_add (h a List.mem_cons_self) (ih fun j hj => h j (List.mem_cons_of_mem _ hj))
    simpa using this

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [FiniteDimensional ℝ H₁]
  [FiniteDimensional ℝ H₂]

/-- **The lift of an `RQ` through the letter matrix.** -/
theorem brq_of_rq (e : OrthonormalBasis (Fin m₁) ℝ H₁) (e' : OrthonormalBasis (Fin m₂) ℝ H₂)
    (M : H₂ →L[ℝ] H₁) {G : (Vec 2 → ℂ) → Vec 2 → ℂ} {B1 B2 B3 B4 : ℝ}
    (h1 : 0 ≤ B1) (h2 : 0 ≤ B2) (h3 : 0 ≤ B3) (h4 : 0 ≤ B4) (h : RQ L n Nmin G B1 B2 B3 B4) :
    BRQ L n Nmin (fun b b' f z => ((letterMat e e' M b b' : ℝ) : ℂ) * G f z) (‖M‖ * B1) (‖M‖ * B2)
      (‖M‖ * B3) (‖M‖ * B4) := by
  obtain ⟨A, hv, n1, n2, n3, n4⟩ := h
  have hA1 : ‖A‖ ≤ B1 := ContinuousLinearMap.opNorm_le_bound _ h1 n1
  have hA2 : ‖(slMeanOp n).comp A‖ ≤ B2 := ContinuousLinearMap.opNorm_le_bound _ h2
    (by simpa [ContinuousLinearMap.comp_apply] using n2)
  have hA3 : ‖A.comp (slConstCLM L)‖ ≤ B3 := ContinuousLinearMap.opNorm_le_bound _ h3
    (by simpa [ContinuousLinearMap.comp_apply] using n3)
  have hA4 : ‖(slMeanOp n).comp (A.comp (slConstCLM L))‖ ≤ B4 :=
    ContinuousLinearMap.opNorm_le_bound _ h4 (by simpa [ContinuousLinearMap.comp_apply] using n4)
  refine ⟨fun b b' => letterMat e e' M b b' • A, fun N hLN hN b b' ψ => ?_,
    (blockBound_mat_smul e e' M A).mono (mul_le_mul_of_nonneg_left hA1 (norm_nonneg _)),
    ?_, ?_, ?_⟩
  · rw [smul_apply, map_smul]
    filter_upwards [Lp.coeFn_smul (letterMat e e' M b b') (torusHkValueCLM (A (truncateTorusHk hLN ψ))),
      hv N hLN hN ψ] with z h1 h2
    rw [h1]
    simp only [Pi.smul_apply, h2, Complex.real_smul]
  · have := (blockBound_mat_smul e e' M ((slMeanOp n).comp A)).mono
      (mul_le_mul_of_nonneg_left hA2 (norm_nonneg _))
    convert this using 3
    ext x
    simp
  · have := (blockBound_mat_smul e e' M (A.comp (slConstCLM L))).mono
      (mul_le_mul_of_nonneg_left hA3 (norm_nonneg _))
    convert this using 3
    ext x
    simp
  · have := (blockBound_mat_smul e e' M ((slMeanOp n).comp (A.comp (slConstCLM L)))).mono
      (mul_le_mul_of_nonneg_left hA4 (norm_nonneg _))
    convert this using 3
    ext x
    simp

end BRQ
end

/-! # one variant of one constituent, filtered by a predicate on the transfer index

`rq_gamP` is the copy of `realizes_gam` for `letterGamP P` at the level `L`, with the four bounds
of `RQ` given as explicit sums `sgSum` of the unit bounds `sgU1 .. sgU4` (the scalar of a unit is
`sgKap P ... = if P a then gamK ... else 0`). -/

section
open Classical in
/-- The scalar of a unit term, zero outside the predicate. -/
def sgKap (P : ℕ × ℕ → Prop) (Rcv δ : ℝ) (d s u v : ℕ) (β₀ w a β' : ℕ × ℕ) : ℝ :=
  if P a then gamK Rcv δ d s u v β₀ w a β' else 0

/-- Norm bound of a unit. -/
def sgU1 (ρ : ℝ) (n : ℕ) (pre : Bool) (p q : ℕ) (Jt κ : ℝ) : ℝ :=
  |κ| * ((1 + ρ) ^ (p + q + preExp pre) * (|cellDriftNativePrice (n + p + q)| * Jt))

/-- Mean bound of a unit. -/
def sgU2 (θ : Vec 2) (ρ : ℝ) (n : ℕ) (pre : Bool) (p q : ℕ) (Jt κ : ℝ) : ℝ :=
  |κ| * (|θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * Jt) *
    (if pre then 1 + ρ else 1))

/-- Norm bound of a unit on constants. -/
def sgU3 (θ : Vec 2) (ρ : ℝ) (n : ℕ) (pre : Bool) (k : Fin 2) (kc : ℝ) (p q : ℕ)
    (Jt κ : ℝ) : ℝ :=
  |κ| * ((1 + ρ) ^ (p + q) * (|cellDriftNativePrice (n + p + q)| * Jt) *
    ((if pre then |θ k| else 1) * kc))

/-- Mean bound of a unit on constants. -/
def sgU4 (θ : Vec 2) (n : ℕ) (pre : Bool) (k : Fin 2) (kc : ℝ) (p q : ℕ) (Jt κ : ℝ) : ℝ :=
  |κ| * (|θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * Jt) *
    ((if pre then |θ k| else 1) * kc))

/-- The sum of a unit bound over the unit terms of a variant. -/
def sgSum (pos : Bool) (slow d : ℕ) (U : DerivativeWord2 (d - 1) → ℕ → ℕ × ℕ → ℕ × ℕ → ℝ) : ℝ :=
  ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.Icc (if pos then 1 else 0) slow,
    ∑ ω : DerivativeWord2 s, ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
        Finset.range ((wordCount α).2 + 1), U α s (wordCount ω) a

theorem sgU1_nonneg (ρ : ℝ) (hρ : 0 ≤ ρ) (n : ℕ) (pre : Bool) (p q : ℕ) (Jt κ : ℝ) (hJ : 0 ≤ Jt) :
    0 ≤ sgU1 ρ n pre p q Jt κ :=
  mul_nonneg (abs_nonneg _) (mul_nonneg (pow_nonneg (by linarith) _)
    (mul_nonneg (abs_nonneg _) hJ))

theorem sgU2_nonneg (θ : Vec 2) (ρ : ℝ) (hρ : 0 ≤ ρ) (n : ℕ) (pre : Bool) (p q : ℕ)
    (Jt κ : ℝ) (hJ : 0 ≤ Jt) : 0 ≤ sgU2 θ ρ n pre p q Jt κ := by
  unfold sgU2
  have : 0 ≤ (if pre then 1 + ρ else 1) := by split_ifs <;> linarith
  positivity

theorem sgU3_nonneg (θ : Vec 2) (ρ : ℝ) (hρ : 0 ≤ ρ) (n : ℕ) (pre : Bool) (k : Fin 2) (kc : ℝ)
    (hkc : 0 ≤ kc) (p q : ℕ) (Jt κ : ℝ) (hJ : 0 ≤ Jt) : 0 ≤ sgU3 θ ρ n pre k kc p q Jt κ := by
  unfold sgU3
  have : 0 ≤ (if pre then |θ k| else 1) := by split_ifs <;> positivity
  have : 0 ≤ (1 + ρ) := by linarith
  positivity

theorem sgU4_nonneg (θ : Vec 2) (n : ℕ) (pre : Bool) (k : Fin 2) (kc : ℝ) (hkc : 0 ≤ kc)
    (p q : ℕ) (Jt κ : ℝ) (hJ : 0 ≤ Jt) : 0 ≤ sgU4 θ n pre k kc p q Jt κ := by
  unfold sgU4
  have : 0 ≤ (if pre then |θ k| else 1) := by split_ifs <;> positivity
  positivity

theorem sgSum_nonneg (pos : Bool) (slow d : ℕ) (U : DerivativeWord2 (d - 1) → ℕ → ℕ × ℕ → ℕ × ℕ → ℝ)
    (hU : ∀ α s w a, 0 ≤ U α s w a) : 0 ≤ sgSum pos slow d U :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => hU _ _ _ _

/-- **A unit term of a variant, with the four bounds.** -/
theorem rq_unitP (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n L Nmin p q : ℕ) (k : Fin 2)
    (pre : Bool) (h1 : n + p + q + preExp pre ≤ L) (h2 : p + q + 3 ≤ Nmin) {c : Vec 2 → ℝ}
    (hc : ContDiff ℝ ((n + p + q : ℕ) : ℕ∞) c) (hp : AVenhance.IsZ2Periodic c) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ l ≤ n + p + q, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (κ : ℝ) :
    RQ L n Nmin (fun f z => (κ : ℂ) * fibreCovPow θ (p, q)
        (fun y => (c y : ℂ) * variantFun pre θ k f y) z)
      (sgU1 ρ n pre p q P κ) (sgU2 θ ρ n pre p q P κ)
      (sgU3 θ ρ n pre k ‖torusHigherConstant L 1‖ p q P κ)
      (sgU4 θ n pre k ‖torusHigherConstant L 1‖ p q P κ) := by
  cases pre
  · have := rq_unit0 θ ρ hθ n L Nmin p q (by simpa [preExp] using h1) h2 hc hp hP0 hP κ
    simp only [variantFun, Bool.false_eq_true, ite_false]
    refine rq_mono this (le_of_eq ?_) (le_of_eq ?_) (le_of_eq ?_) (le_of_eq ?_)
    all_goals simp only [sgU1, sgU2, sgU3, sgU4, preExp, ite_false, Bool.false_eq_true]
    all_goals try ring
  · have := rq_unit1 θ ρ hθ n L Nmin p q k (by simpa [preExp] using h1) h2 hc hp hP0 hP κ
    simp only [variantFun, ite_true]
    refine rq_mono this (le_of_eq ?_) (le_of_eq ?_) (le_of_eq ?_) (le_of_eq ?_)
    all_goals simp only [sgU1, sgU2, sgU3, sgU4, preExp, ite_true]
    all_goals try ring

open Classical in
theorem star_gamP_alpha (P : ℕ × ℕ → Prop) (θ : Vec 2) (d s : ℕ) (δ : ℝ) (u v : ℕ)
    (β₀ w β' : ℕ × ℕ) (c : Vec 2 → ℝ) (fv : Vec 2 → ℂ) (Rcv : ℝ)
    (hb : ∀ a ∈ Finset.range (u + 1) ×ˢ Finset.range (v + 1),
      ContDiff ℝ ((u - a.1) + (v - a.2) : ℕ) (fun y => (c y : ℂ) * fv y)) (z : Vec 2) :
    (Rcv : ℂ) * star ((((δ ^ s / (s.factorial : ℝ)) : ℝ) : ℂ) *
      ((-1 : ℂ) ^ (d - 1) * ∑ a ∈ Finset.range (u + 1) ×ˢ Finset.range (v + 1),
        if β' = (β₀.1 + w.1 - a.1, β₀.2 + w.2 - a.2) ∧ P a then
          ((gamCoefNat u v β₀ w a : ℕ) : ℂ) *
            fibreCovPow (-θ) (u - a.1, v - a.2) (fun z' => (c z' : ℂ) * star (fv z')) z
        else 0)) =
    ∑ a ∈ Finset.range (u + 1) ×ˢ Finset.range (v + 1),
      ((sgKap P Rcv δ d s u v β₀ w a β' : ℝ) : ℂ) *
        fibreCovPow θ (u - a.1, v - a.2) (fun y => (c y : ℂ) * fv y) z := by
  simp only [star_mul', star_sum, Complex.star_def, Complex.conj_ofReal, star_pow, star_neg,
    star_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hcov := star_covPow_term θ (u - a.1, v - a.2) c (hb a ha) z
  rw [Complex.star_def] at hcov
  unfold sgKap gamK
  by_cases hP : P a
  · by_cases h1 : β' = (β₀.1 + w.1 - a.1, β₀.2 + w.2 - a.2)
    · by_cases h2 : a.1 ≤ β₀.1 + w.1 ∧ a.2 ≤ β₀.2 + w.2
      · subst h1
        have hc : gamCond β₀ w a (β₀.1 + w.1 - a.1, β₀.2 + w.2 - a.2) := ⟨rfl, h2⟩
        simp only [hP, and_self, ite_true, hc, map_mul, map_natCast]
        rw [hcov]
        push_cast
        ring
      · have hc : ¬ gamCond β₀ w a β' := fun hh => h2 ⟨hh.2.1, hh.2.2⟩
        simp [hc, gamCoefNat_eq_zero u v β₀ w a h2, hP]
    · have hc : ¬ gamCond β₀ w a β' := fun hh => h1 hh.1
      simp [h1, hc, hP]
  · simp [hP]

/-- **One variant of one constituent, filtered by `P`, is realized with the four bounds.** -/
theorem rq_gamP (P : ℕ × ℕ → Prop) (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n L Nmin J : ℕ)
    (d : ℕ) (hd2 : 2 ≤ d) (hnd : n + d ≤ J) (hL1 : n + d ≤ L) (hNmin : d + 3 ≤ Nmin)
    (pos : Bool) (slow : ℕ) (δ : ℝ) (X₀ : Vec 2) (r : ℝ)
    (coeff : DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec 2 → Vec 2)
    (jet : DerivativeWord2 (d - 1) → ℕ → ℕ → ℝ) (hjet0 : ∀ α s l, 0 ≤ jet α s l)
    (hfacts : ∀ α s, s ≤ slow → ∀ (ω : DerivativeWord2 s) (k' : Fin 2),
      ContDiff ℝ (J : ℕ∞) (tbTermCoef (coeff α r) s ω X₀ k') ∧
      AVenhance.IsZ2Periodic (tbTermCoef (coeff α r) s ω X₀ k') ∧
      ∀ l ≤ J, ∀ z, ‖iteratedFDeriv ℝ l (tbTermCoef (coeff α r) s ω X₀ k') z‖ ≤ jet α s l)
    (Rcv : ℝ) (β₀ : ℕ × ℕ) (k : Fin 2) (β' : ℕ × ℕ) (pre : Bool) :
    RQ L n Nmin (fun f z => (Rcv : ℂ) * star (letterGamP P θ pos slow δ X₀ r d coeff β₀ k β'
        (variantFun pre (-θ) k (fun y => star (f y))) z))
      (sgSum pos slow d (fun α s w a => sgU1 ρ n pre ((wordCount α).1 - a.1)
        ((wordCount α).2 - a.2) (∑ l ∈ Finset.range (J + 1), jet α s l)
        (sgKap P Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ w a β')))
      (sgSum pos slow d (fun α s w a => sgU2 θ ρ n pre ((wordCount α).1 - a.1)
        ((wordCount α).2 - a.2) (∑ l ∈ Finset.range (J + 1), jet α s l)
        (sgKap P Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ w a β')))
      (sgSum pos slow d (fun α s w a => sgU3 θ ρ n pre k ‖torusHigherConstant L 1‖
        ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (∑ l ∈ Finset.range (J + 1), jet α s l)
        (sgKap P Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ w a β')))
      (sgSum pos slow d (fun α s w a => sgU4 θ n pre k ‖torusHigherConstant L 1‖
        ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (∑ l ∈ Finset.range (J + 1), jet α s l)
        (sgKap P Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ w a β'))) := by
  classical
  have hd1 : d - 1 + 1 = d := by omega
  have unit : ∀ (α : DerivativeWord2 (d - 1)) (s : ℕ), s ≤ slow → ∀ (ω : DerivativeWord2 s)
      (a : ℕ × ℕ), a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ Finset.range ((wordCount α).2 + 1) →
      RQ L n Nmin (fun f z => ((sgKap P Rcv δ d s (wordCount α).1 (wordCount α).2 β₀
          (wordCount ω) a β' : ℝ) : ℂ) * fibreCovPow θ ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
          (fun y => (tbTermCoef (coeff α r) s ω X₀ k y : ℂ) * variantFun pre θ k f y) z)
        (sgU1 ρ n pre ((wordCount α).1 - a.1) ((wordCount α).2 - a.2)
          (∑ l ∈ Finset.range (J + 1), jet α s l)
          (sgKap P Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β'))
        (sgU2 θ ρ n pre ((wordCount α).1 - a.1) ((wordCount α).2 - a.2)
          (∑ l ∈ Finset.range (J + 1), jet α s l)
          (sgKap P Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β'))
        (sgU3 θ ρ n pre k ‖torusHigherConstant L 1‖ ((wordCount α).1 - a.1)
          ((wordCount α).2 - a.2) (∑ l ∈ Finset.range (J + 1), jet α s l)
          (sgKap P Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β'))
        (sgU4 θ n pre k ‖torusHigherConstant L 1‖ ((wordCount α).1 - a.1)
          ((wordCount α).2 - a.2) (∑ l ∈ Finset.range (J + 1), jet α s l)
          (sgKap P Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β')) := by
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
    exact rq_unitP θ ρ hθ n L Nmin ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) k pre
      (by cases pre <;> simp [preExp] <;> omega) (by omega) hc' hp
      (Finset.sum_nonneg fun l _ => hjet0 α s l) hP _
  have hsum := rq_finset_sum (L := L) (n := n) (Nmin := Nmin) Finset.univ
    (fun (α : DerivativeWord2 (d - 1)) _ =>
      rq_finset_sum (Finset.Icc (if pos then 1 else 0) slow) (fun s hs =>
        rq_finset_sum (Finset.univ : Finset (DerivativeWord2 s)) (fun ω _ =>
          rq_finset_sum (Finset.range ((wordCount α).1 + 1) ×ˢ Finset.range ((wordCount α).2 + 1))
            (fun a ha => unit α s (Finset.mem_Icc.1 hs).2 ω a ha))))
  refine rq_congr hsum (fun N hLN hN ψ => ?_)
  funext z
  have hcd : ContDiff ℝ (d : ℕ∞) (torusHigherClassicalValue N ψ) :=
    torusHigherClassicalValue_contDiff N d (by omega) ψ
  have hdiff : Differentiable ℝ (torusHigherClassicalValue N ψ) :=
    (hcd.of_le (by exact_mod_cast (by omega : 1 ≤ d))).differentiable one_ne_zero
  have hfv : ContDiff ℝ ((d - 1 : ℕ) : ℕ∞) (variantFun pre θ k (torusHigherClassicalValue N ψ)) :=
    contDiff_variantFun pre θ k (m := d - 1) (by rw [hd1]; exact hcd)
  rw [variantFun_star pre θ k hdiff]
  unfold letterGamP
  rw [star_sum, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun α _ => ?_).symm
  rw [star_sum, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun s hs => ?_)
  rw [star_sum, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun ω _ => ?_)
  have hwc := wordCount_sum α
  have key := star_gamP_alpha P θ d s δ (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) β'
    (tbTermCoef (coeff α r) s ω X₀ k) (variantFun pre θ k (torusHigherClassicalValue N ψ)) Rcv
    (fun a ha => by
      obtain ⟨hc, -, -⟩ := hfacts α s (Finset.mem_Icc.1 hs).2 ω k
      have hle : (wordCount α).1 - a.1 + ((wordCount α).2 - a.2) ≤ J := by omega
      have hle2 : (wordCount α).1 - a.1 + ((wordCount α).2 - a.2) ≤ d - 1 := by omega
      exact contDiff_real_mul_complex (m := (wordCount α).1 - a.1 + ((wordCount α).2 - a.2))
        (hc.of_le (by exact_mod_cast hle)) (hfv.of_le (by exact_mod_cast hle2))) z
  exact key
end

/-! # the kernel bound of a unit scalar with the exact power of `ϖ`

`scale_le`, `gamK_le`: the scale and kernel bounds that keep the power `ϖ ^ (|β| - |β₀| + |a|)`
instead of one factor `ϖ`.  `kap_le` is the same for the filtered
scalar `sgKap`. -/

section
universe u v

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {D Nw : ℕ}

theorem scale_le (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (l : Fin Nw) (x x' : ι) (β β' β0 a : ℕ × ℕ) (s : ℕ)
    (hx : 0 < π x) (hx' : 0 < π x') (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1)
    (hθ : 0 < (letters l).theta) (hs : (if (letters l).positive then 1 else 0) ≤ s)
    (hexp : β'.1 + β'.2 + (a.1 + a.2) = β0.1 + β0.2 + s) (hb0 : β0.1 + β0.2 ≤ β.1 + β.2)
    :
    |letterRatioReal π ϖ ηg letters l x x' β β' * ((ϖ * ηg) ^ s / (s.factorial : ℝ))| ≤
      ϖ ^ (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2)) * (Real.sqrt (π x' / π x) * ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / (letters l).theta) := by
  have hE := pow_ratio_mul ϖ hϖ0 (β.1 + β.2) (β'.1 + β'.2) s (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2))
    (by omega)
  have hEle : ϖ ^ (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2)) ≤ 1 := pow_le_one₀ hϖ0.le hϖ1
  obtain ⟨hf0, hf1⟩ := eta_fac_le ηg (letters l).theta (letters l).positive s hg0 hg1 hθ hs
  have hF : (1 : ℝ) ≤ ((β.1.factorial * β.2.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have hF' : (0 : ℝ) ≤ ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsf : (1 : ℝ) ≤ (s.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have hal : letterAlive ηg letters l = 0 ∨ letterAlive ηg letters l = 1 := by
    unfold letterAlive; split_ifs <;> simp
  have hsq : 0 ≤ Real.sqrt (π x' / π x) := Real.sqrt_nonneg _
  have eq : letterRatioReal π ϖ ηg letters l x x' β β' * ((ϖ * ηg) ^ s / (s.factorial : ℝ)) =
      letterAlive ηg letters l * Real.sqrt (π x' / π x) *
        (ϖ ^ (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2)) *
          (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
          (ηg ^ s * (letterFac ηg letters l)⁻¹) / (s.factorial : ℝ)) := by
    unfold letterRatioReal
    rw [piRatio_eq_sqrt π x x' hx hx', ← hE, mul_pow]
    unfold letterFac
    ring
  rw [eq]
  have hq : 0 ≤ ϖ ^ (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2)) *
          (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
          (ηg ^ s * (letterFac ηg letters l)⁻¹) / (s.factorial : ℝ) := by
    have := pow_nonneg hϖ0.le (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2))
    positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hsq, abs_of_nonneg hq]
  have hal1 : |letterAlive ηg letters l| ≤ 1 := by rcases hal with h | h <;> simp [h]
  have hq1 : ϖ ^ (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2)) *
          (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
          (ηg ^ s * (letterFac ηg letters l)⁻¹) / (s.factorial : ℝ) ≤
        ϖ ^ (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2)) * (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / (letters l).theta) := by
    have hd : (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ))
        ≤ ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) := div_le_self hF' hF
    have hdn : 0 ≤ (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) /
        ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) := by positivity
    have hp0 := pow_nonneg hϖ0.le (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2))
    calc _ ≤ ϖ ^ (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2)) *
          (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
          (ηg ^ s * (letterFac ηg letters l)⁻¹) := div_le_self (by positivity) hsf
      _ ≤ ϖ ^ (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2)) * ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) * (letters l).theta⁻¹ := by
          have h1 : ηg ^ s * (letterFac ηg letters l)⁻¹ ≤ (letters l).theta⁻¹ := hf1
          have h2 : ηg ^ s * (letterFac ηg letters l)⁻¹ ≥ 0 := hf0
          gcongr
      _ = _ := by rw [div_eq_mul_inv, mul_assoc]
  calc |letterAlive ηg letters l| * Real.sqrt (π x' / π x) * _ ≤
      1 * Real.sqrt (π x' / π x) * (ϖ ^ (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2)) * (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) /
        (letters l).theta)) := by gcongr
    _ = _ := by ring



theorem gamK_le (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw)
    (x x' : ι) (β β' β₀ w a : ℕ × ℕ) (s d u v M0 slow Dm : ℕ) (cv : ℝ) (hcv : |cv| ≤ (M0 : ℝ) + 1)
    (hx : 0 < π x) (hx' : 0 < π x') (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1)
    (hθ : 0 < (letters l).theta) (hs : (if (letters l).positive then 1 else 0) ≤ s)
    (hsl : s ≤ slow) (hw : w.1 + w.2 = s) (hb0 : β₀.1 + β₀.2 ≤ β.1 + β.2)
    (hβM : β.1 + β.2 ≤ M0) (hβ'M : β'.1 + β'.2 ≤ M0) (hu : u ≤ Dm) (hv : v ≤ Dm)
    (hau : a.1 ≤ u) (hav : a.2 ≤ v) :
    |gamK (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s u v β₀ w a β'| ≤
      ϖ ^ (β.1 + β.2 - (β₀.1 + β₀.2) + (a.1 + a.2)) * (gamCc Dm M0 slow * (Real.sqrt (π x' / π x) / (letters l).theta)) := by
  have hCc := gamCc_nonneg Dm M0 slow
  have hsq : 0 ≤ Real.sqrt (π x' / π x) / (letters l).theta := by positivity
  unfold gamK
  by_cases hc : gamCond β₀ w a β'
  · obtain ⟨h1, h2, h3⟩ := hc
    have e1 : β'.1 = β₀.1 + w.1 - a.1 := by rw [h1]
    have e2 : β'.2 = β₀.2 + w.2 - a.2 := by rw [h1]
    have hexp : β'.1 + β'.2 + (a.1 + a.2) = β₀.1 + β₀.2 + s := by omega
    have hsc := scale_le π ϖ ηg letters l x x' β β' β₀ a s hx hx' hϖ0 hϖ1 hg0 hg1 hθ hs
      hexp hb0
    have hfa : (((β'.1.factorial * β'.2.factorial : ℕ)) : ℝ) ≤ ((M0.factorial : ℕ) : ℝ) := by
      exact_mod_cast factorial_pair_le _ _ _ hβ'M
    have hcoef : ((gamCoefNat u v β₀ w a : ℕ) : ℝ) ≤ ((2 : ℝ) ^ Dm) ^ 2 *
        (((M0 + slow + 1 : ℕ) : ℝ) ^ Dm) ^ 2 := by
      have := gamCoefNat_le u v Dm M0 slow β₀ w a hu hv hau hav (by omega) (by omega)
      exact_mod_cast this
    have hgc : gamCond β₀ w a β' := ⟨h1, h2, h3⟩
    simp only [hgc, ite_true]
    have hrw : letterRatioReal π ϖ ηg letters l x x' β β' * cv *
        ((ϖ * ηg) ^ s / (s.factorial : ℝ) * ((-1 : ℝ) ^ (d - 1) * (gamCoefNat u v β₀ w a : ℝ))) =
        (letterRatioReal π ϖ ηg letters l x x' β β' * ((ϖ * ηg) ^ s / (s.factorial : ℝ))) * cv *
          ((-1 : ℝ) ^ (d - 1) * (gamCoefNat u v β₀ w a : ℝ)) := by ring
    rw [hrw]
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    have hsc' : |letterRatioReal π ϖ ηg letters l x x' β β' * ((ϖ * ηg) ^ s / (s.factorial : ℝ))| ≤
        ϖ ^ (β.1 + β.2 - (β₀.1 + β₀.2) + (a.1 + a.2)) * (Real.sqrt (π x' / π x) * ((M0.factorial : ℕ) : ℝ) / (letters l).theta) :=
      hsc.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfa (Real.sqrt_nonneg _)) hθ.le) (pow_nonneg hϖ0.le _))
    rw [abs_mul] at hsc'
    calc _ ≤ (ϖ ^ (β.1 + β.2 - (β₀.1 + β₀.2) + (a.1 + a.2)) * (Real.sqrt (π x' / π x) * ((M0.factorial : ℕ) : ℝ) / (letters l).theta)) *
          ((M0 : ℝ) + 1) * (((2 : ℝ) ^ Dm) ^ 2 * (((M0 + slow + 1 : ℕ) : ℝ) ^ Dm) ^ 2) := by
          gcongr
      _ = _ := by unfold gamCc; ring
  · simp only [hc, ite_false, mul_zero, abs_zero]
    positivity



theorem kap_le (P : ℕ × ℕ → Prop) (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (l : Fin Nw)
    (x x' : ι) (β β' β₀ w a : ℕ × ℕ) (s d u v M0 slow Dm : ℕ) (cv : ℝ) (hcv : |cv| ≤ (M0 : ℝ) + 1)
    (hx : 0 < π x) (hx' : 0 < π x') (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1)
    (hθ : 0 < (letters l).theta) (hs : (if (letters l).positive then 1 else 0) ≤ s)
    (hsl : s ≤ slow) (hw : w.1 + w.2 = s) (hb0 : β₀.1 + β₀.2 ≤ β.1 + β.2)
    (hβM : β.1 + β.2 ≤ M0) (hβ'M : β'.1 + β'.2 ≤ M0) (hu : u ≤ Dm) (hv : v ≤ Dm)
    (hau : a.1 ≤ u) (hav : a.2 ≤ v) :
    |sgKap P (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s u v β₀ w a β'| ≤
      ϖ ^ (β.1 + β.2 - (β₀.1 + β₀.2) + (a.1 + a.2)) *
        (gamCc Dm M0 slow * (Real.sqrt (π x' / π x) / (letters l).theta)) := by
  classical
  unfold sgKap
  split_ifs
  · exact gamK_le π ϖ ηg letters l x x' β β' β₀ w a s d u v M0 slow Dm cv hcv hx hx' hϖ0 hϖ1
      hg0 hg1 hθ hs hsl hw hb0 hβM hβ'M hu hv hau hav
  · rw [abs_zero]
    have := gamCc_nonneg Dm M0 slow
    have hsq : 0 ≤ Real.sqrt (π x' / π x) / (letters l).theta := by positivity
    positivity

theorem kap_zero (P : ℕ × ℕ → Prop) (R δ : ℝ) (d s u v : ℕ) (β₀ w a β' : ℕ × ℕ) :
    sgKap P (R * 0) δ d s u v β₀ w a β' = 0 := by
  classical
  unfold sgKap gamK
  simp

theorem kap_of_not (P : ℕ × ℕ → Prop) (R δ : ℝ) (d s u v : ℕ) (β₀ w a β' : ℕ × ℕ)
    (hP : ¬ P a) : sgKap P R δ d s u v β₀ w a β' = 0 := by
  classical
  unfold sgKap
  simp [hP]
end

/-! # unit-term numerics

Pure real lemmas: the four unit bounds `sgU1 .. sgU4` of a unit whose scalar satisfies
`|κ| ≤ ϖ^E c0` are bounded by `ϖ`, `t`, `t kc`, `ζ² kc` times `c0 R^Dm Pr Jt` (`R = 1 + ρ`),
in the gain case (`1 ≤ E`) and in the zero case (`E = 0`, a derivative variant). -/

section
theorem pow_zeta {ϖ ζ t R : ℝ} (E m : ℕ) (hϖ0 : 0 ≤ ϖ) (hϖζ : ϖ ≤ ζ) (hζ1 : ζ ≤ 1)
    (ht0 : 0 ≤ t) (htζ : t ≤ R * ζ) (hR : 1 ≤ R) (hE : 1 ≤ E) (hEm : 2 ≤ E ∨ 1 ≤ m) :
    ϖ ^ E * t ^ m ≤ R ^ m * ζ ^ 2 := by
  have hζ0 : 0 ≤ ζ := hϖ0.trans hϖζ
  have hR0 : 0 ≤ R := by linarith
  have htR : t ≤ R := htζ.trans (mul_le_of_le_one_right hR0 hζ1)
  have htm : ∀ j : ℕ, t ^ j ≤ R ^ j := fun j => pow_le_pow_left₀ ht0 htR j
  have hϖ1 : ϖ ≤ 1 := hϖζ.trans hζ1
  rcases hEm with h2 | h1
  · have h3 : ϖ ^ E ≤ ζ ^ 2 :=
      (pow_le_pow_of_le_one hϖ0 hϖ1 h2).trans (pow_le_pow_left₀ hϖ0 hϖζ 2)
    calc ϖ ^ E * t ^ m ≤ ζ ^ 2 * R ^ m :=
          mul_le_mul h3 (htm m) (pow_nonneg ht0 _) (sq_nonneg _)
      _ = R ^ m * ζ ^ 2 := by ring
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h3 : ϖ ^ E ≤ ζ := (pow_le_of_le_one hϖ0 hϖ1 (by omega)).trans hϖζ
    have h4 : t ^ (m' + 1) ≤ (R * ζ) * R ^ m' := by
      rw [pow_succ']
      exact mul_le_mul htζ (htm m') (pow_nonneg ht0 _) (by positivity)
    calc ϖ ^ E * t ^ (m' + 1) ≤ ζ * ((R * ζ) * R ^ m') :=
          mul_le_mul h3 h4 (pow_nonneg ht0 _) hζ0
      _ = R ^ (m' + 1) * ζ ^ 2 := by ring

theorem t_sq {ζ t R : ℝ} (m : ℕ) (hζ1 : ζ ≤ 1) (hζ0 : 0 ≤ ζ) (ht0 : 0 ≤ t)
    (htζ : t ≤ R * ζ) (hR : 1 ≤ R) (hm : 2 ≤ m) : t ^ m ≤ R ^ m * ζ ^ 2 := by
  have hR0 : 0 ≤ R := by linarith
  have htR : t ≤ R := htζ.trans (mul_le_of_le_one_right hR0 hζ1)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  calc t ^ (m' + 2) = (t * t) * t ^ m' := by ring
    _ ≤ ((R * ζ) * (R * ζ)) * R ^ m' :=
        mul_le_mul (mul_le_mul htζ htζ ht0 (by positivity)) (pow_le_pow_left₀ ht0 htR m')
          (pow_nonneg ht0 _) (by positivity)
    _ = R ^ (m' + 2) * ζ ^ 2 := by ring

theorem theta_pow (θ : Vec 2) (t : ℝ) (h : ∀ j, |θ j| ≤ t) (pre : Bool) (k : Fin 2)
    (p q : ℕ) : |θ 0| ^ p * |θ 1| ^ q * (if pre then |θ k| else 1) ≤ t ^ (p + q + preExp pre) := by
  have ht0 : 0 ≤ t := (abs_nonneg _).trans (h 0)
  have h01 : |θ 0| ^ p * |θ 1| ^ q ≤ t ^ p * t ^ q :=
    mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (h 0) p) (pow_le_pow_left₀ (abs_nonneg _) (h 1) q)
      (by positivity) (by positivity)
  cases pre
  · simp only [Bool.false_eq_true, ite_false, mul_one, preExp, add_zero]
    rwa [pow_add]
  · simp only [ite_true, preExp]
    rw [pow_add, pow_add, pow_one]
    exact mul_le_mul h01 (h k) (abs_nonneg _) (by positivity)

section Units

variable {ρ t ζ ϖ : ℝ} {n Dm p q : ℕ} {pre : Bool} {k : Fin 2} {θ : Vec 2}
  {Jt κ c0 Pr kc E : ℝ}

/-- Gain norm bound of a unit. -/
theorem gain_u1 (hρ : 0 ≤ ρ) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1) (hc0 : 0 ≤ c0) (hJ : 0 ≤ Jt)
    (Ex : ℕ) (hEx : 1 ≤ Ex) (hκ : |κ| ≤ ϖ ^ Ex * c0) (hpq : p + q + preExp pre ≤ Dm)
    (hPr : |cellDriftNativePrice (n + p + q)| ≤ Pr) :
    sgU1 ρ n pre p q Jt κ ≤ ϖ * (c0 * ((1 + ρ) ^ Dm * Pr) * Jt) := by
  have h1 : |κ| ≤ ϖ * c0 :=
    hκ.trans (mul_le_mul_of_nonneg_right (pow_le_of_le_one hϖ0 hϖ1 (by omega)) hc0)
  have h2 : (1 + ρ) ^ (p + q + preExp pre) ≤ (1 + ρ) ^ Dm :=
    pow_le_pow_right₀ (by linarith) hpq
  unfold sgU1
  calc _ ≤ (ϖ * c0) * ((1 + ρ) ^ Dm * (Pr * Jt)) := by gcongr
    _ = _ := by ring

/-- Gain mean-on-constants bound of a unit. -/
theorem gain_u4 (hρ : 0 ≤ ρ) (hϖ0 : 0 ≤ ϖ) (hϖζ : ϖ ≤ ζ) (hζ1 : ζ ≤ 1) (ht0 : 0 ≤ t)
    (htζ : t ≤ (1 + ρ) * ζ) (hθ : ∀ j, |θ j| ≤ t) (hc0 : 0 ≤ c0) (hJ : 0 ≤ Jt) (hkc : 0 ≤ kc)
    (Ex : ℕ) (hEx : 1 ≤ Ex) (hEm : 2 ≤ Ex ∨ 1 ≤ p + q + preExp pre)
    (hκ : |κ| ≤ ϖ ^ Ex * c0) (hpq : p + q + preExp pre ≤ Dm)
    (hPr : |cellDriftNativePrice (n + p + q)| ≤ Pr) :
    sgU4 θ n pre k kc p q Jt κ ≤ ζ ^ 2 * kc * (c0 * ((1 + ρ) ^ Dm * Pr) * Jt) := by
  have hT := theta_pow θ t hθ pre k p q
  have hZ := pow_zeta (ϖ := ϖ) (ζ := ζ) (t := t) (R := 1 + ρ) Ex (p + q + preExp pre) hϖ0 hϖζ
    hζ1 ht0 htζ (by linarith) hEx hEm
  have h2 : (1 + ρ) ^ (p + q + preExp pre) ≤ (1 + ρ) ^ Dm :=
    pow_le_pow_right₀ (by linarith) hpq
  have hϖE : 0 ≤ ϖ ^ Ex := pow_nonneg hϖ0 _
  have hζ0 : 0 ≤ ζ := hϖ0.trans hϖζ
  have h3 : ϖ ^ Ex * t ^ (p + q + preExp pre) ≤ (1 + ρ) ^ Dm * ζ ^ 2 :=
    hZ.trans (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
  unfold sgU4
  have e : |κ| * (|θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * Jt) *
      ((if pre then |θ k| else 1) * kc)) =
      |κ| * ((|θ 0| ^ p * |θ 1| ^ q * (if pre then |θ k| else 1)) *
        (|cellDriftNativePrice (n + p + q)| * Jt * kc)) := by ring
  rw [e]
  have h4 : |κ| * (|θ 0| ^ p * |θ 1| ^ q * (if pre then |θ k| else 1)) ≤
      c0 * ((1 + ρ) ^ Dm * ζ ^ 2) := by
    calc _ ≤ (ϖ ^ Ex * c0) * t ^ (p + q + preExp pre) :=
          mul_le_mul hκ hT (by positivity) (by positivity)
      _ = c0 * (ϖ ^ Ex * t ^ (p + q + preExp pre)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hc0
  calc _ = (|κ| * (|θ 0| ^ p * |θ 1| ^ q * (if pre then |θ k| else 1))) *
        (|cellDriftNativePrice (n + p + q)| * Jt * kc) := by ring
    _ ≤ (c0 * ((1 + ρ) ^ Dm * ζ ^ 2)) * (Pr * Jt * kc) := by gcongr
    _ = _ := by ring

/-- Zero-case mean bound of a derivative unit with `p + q ≥ 1` twists. -/
theorem zero_u2 (hρ : 0 ≤ ρ) (ht0 : 0 ≤ t) (htρ : t ≤ ρ) (hθ : ∀ j, |θ j| ≤ t) (hc0 : 0 ≤ c0)
    (hJ : 0 ≤ Jt) (hκ : |κ| ≤ c0) (hpq1 : 1 ≤ p + q) (hpq : p + q + 1 ≤ Dm)
    (hPr : |cellDriftNativePrice (n + p + q)| ≤ Pr) :
    sgU2 θ ρ n true p q Jt κ ≤ t * (c0 * ((1 + ρ) ^ Dm * Pr) * Jt) := by
  have hθp : |θ 0| ^ p * |θ 1| ^ q ≤ t ^ p * t ^ q :=
    mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hθ 0) p) (pow_le_pow_left₀ (abs_nonneg _) (hθ 1) q)
      (by positivity) (by positivity)
  obtain ⟨m', hm'⟩ : ∃ m', p + q = m' + 1 := ⟨p + q - 1, by omega⟩
  have h5 : t ^ p * t ^ q ≤ t * (1 + ρ) ^ m' := by
    rw [← pow_add, hm', pow_succ']
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 (htρ.trans (by linarith)) m') ht0
  have h6 : (1 + ρ) ^ m' * (1 + ρ) ≤ (1 + ρ) ^ Dm := by
    rw [← pow_succ]; exact pow_le_pow_right₀ (by linarith) (by omega)
  have hPr0 : 0 ≤ Pr := (abs_nonneg _).trans hPr
  unfold sgU2
  simp only [ite_true]
  have h7 : |θ 0| ^ p * |θ 1| ^ q ≤ t * (1 + ρ) ^ m' := hθp.trans h5
  calc _ ≤ c0 * ((t * (1 + ρ) ^ m') * (Pr * Jt) * (1 + ρ)) := by gcongr
    _ = t * (c0 * ((1 + ρ) ^ m' * (1 + ρ)) * Pr * Jt) := by ring
    _ ≤ _ := by
        have : c0 * ((1 + ρ) ^ m' * (1 + ρ)) ≤ c0 * (1 + ρ) ^ Dm :=
          mul_le_mul_of_nonneg_left h6 hc0
        calc t * (c0 * ((1 + ρ) ^ m' * (1 + ρ)) * Pr * Jt) ≤ t * (c0 * (1 + ρ) ^ Dm * Pr * Jt) := by
              gcongr
          _ = _ := by ring

/-- Zero-case norm-on-constants bound of a derivative unit. -/
theorem zero_u3 (hρ : 0 ≤ ρ) (hθ : ∀ j, |θ j| ≤ t) (hc0 : 0 ≤ c0) (hJ : 0 ≤ Jt)
    (hkc : 0 ≤ kc) (hκ : |κ| ≤ c0) (hpq : p + q ≤ Dm)
    (hPr : |cellDriftNativePrice (n + p + q)| ≤ Pr) :
    sgU3 θ ρ n true k kc p q Jt κ ≤ t * kc * (c0 * ((1 + ρ) ^ Dm * Pr) * Jt) := by
  have h2 : (1 + ρ) ^ (p + q) ≤ (1 + ρ) ^ Dm := pow_le_pow_right₀ (by linarith) hpq
  have ht0 : 0 ≤ t := (abs_nonneg _).trans (hθ 0)
  have hPr0 : 0 ≤ Pr := (abs_nonneg _).trans hPr
  unfold sgU3
  simp only [ite_true]
  have := hθ k
  calc _ ≤ c0 * ((1 + ρ) ^ Dm * (Pr * Jt) * (t * kc)) := by gcongr
    _ = _ := by ring

/-- Zero-case mean-on-constants bound of a derivative unit with `p + q ≥ 1` twists. -/
theorem zero_u4 (hρ : 0 ≤ ρ) (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (ht0 : 0 ≤ t)
    (htζ : t ≤ (1 + ρ) * ζ) (hθ : ∀ j, |θ j| ≤ t) (hc0 : 0 ≤ c0) (hJ : 0 ≤ Jt) (hkc : 0 ≤ kc)
    (hκ : |κ| ≤ c0) (hpq1 : 1 ≤ p + q) (hpq : p + q + 1 ≤ Dm)
    (hPr : |cellDriftNativePrice (n + p + q)| ≤ Pr) :
    sgU4 θ n true k kc p q Jt κ ≤ ζ ^ 2 * kc * (c0 * ((1 + ρ) ^ Dm * Pr) * Jt) := by
  have hT := theta_pow θ t hθ true k p q
  have hZ := t_sq (ζ := ζ) (t := t) (R := 1 + ρ) (p + q + preExp true) hζ1 hζ0 ht0 htζ
    (by linarith) (by simp [preExp]; omega)
  have h2 : (1 + ρ) ^ (p + q + preExp true) ≤ (1 + ρ) ^ Dm :=
    pow_le_pow_right₀ (by linarith) (by simpa [preExp] using hpq)
  have h3 : t ^ (p + q + preExp true) ≤ (1 + ρ) ^ Dm * ζ ^ 2 :=
    hZ.trans (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
  unfold sgU4
  have e : |κ| * (|θ 0| ^ p * |θ 1| ^ q * (|cellDriftNativePrice (n + p + q)| * Jt) *
      ((if true then |θ k| else 1) * kc)) =
      |κ| * ((|θ 0| ^ p * |θ 1| ^ q * (if true then |θ k| else 1)) *
        (|cellDriftNativePrice (n + p + q)| * Jt * kc)) := by ring
  rw [e]
  have h4 : |κ| * (|θ 0| ^ p * |θ 1| ^ q * (if true then |θ k| else 1)) ≤
      c0 * ((1 + ρ) ^ Dm * ζ ^ 2) :=
    mul_le_mul hκ (hT.trans h3) (by positivity) hc0
  calc _ = (|κ| * (|θ 0| ^ p * |θ 1| ^ q * (if true then |θ k| else 1))) *
        (|cellDriftNativePrice (n + p + q)| * Jt * kc) := by ring
    _ ≤ (c0 * ((1 + ρ) ^ Dm * ζ ^ 2)) * (Pr * Jt * kc) := by gcongr
    _ = _ := by ring

end Units
end

/-! # the four bounds of one variant of one constituent

`sgSum_le` sums a termwise bound over the unit terms. The gain variant (`P = slSel true β β₀`) is
bounded in norm by `ϖ` and in mean on constants by `ζ² kc`. The zero variant
(`P = slSel false β β₀`) is bounded in mean by `t`, in norm on constants by `t kc` and in mean on
constants by `ζ² kc`. The constant is `gamCfin Dm n ρ M0 Sm` times `√(π x'/π x)/θ` times the jet
total. -/

theorem sgSum_le (pos : Bool) (slow Sm d Dm : ℕ) (hd : d ≤ Dm) (hSm : slow ≤ Sm)
    (U : DerivativeWord2 (d - 1) → ℕ → ℕ × ℕ → ℕ × ℕ → ℝ)
    (Jet : DerivativeWord2 (d - 1) → ℕ → ℝ) (X : ℝ) (hX : 0 ≤ X) (hJ : ∀ α s, 0 ≤ Jet α s)
    (hU : ∀ α s, s ∈ Finset.Icc (if pos then 1 else 0) slow → ∀ ω : DerivativeWord2 s,
      ∀ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ Finset.range ((wordCount α).2 + 1),
        U α s (wordCount ω) a ≤ X * Jet α s) :
    sgSum pos slow d U ≤ (2 : ℝ) ^ Sm * ((Dm : ℝ) + 1) ^ 2 * X *
      ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range (slow + 1), Jet α s := by
  classical
  have hcardw : ∀ s : ℕ, (Fintype.card (DerivativeWord2 s) : ℝ) = 2 ^ s := by
    intro s; simp [DerivativeWord2, DerivativeWord]
  unfold sgSum
  calc _ ≤ ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.Icc (if pos then 1 else 0) slow,
        ∑ ω : DerivativeWord2 s, ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
          Finset.range ((wordCount α).2 + 1), X * Jet α s :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun ω _ =>
          Finset.sum_le_sum fun a ha => hU α s hs ω a ha
    _ ≤ ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.Icc (if pos then 1 else 0) slow,
        (2 : ℝ) ^ Sm * ((Dm : ℝ) + 1) ^ 2 * X * Jet α s := by
        refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun s hs => ?_
        have hwa := wordCount_sum α
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Finset.card_product,
          Finset.card_range, hcardw]
        have hP := hJ α s
        have hs2 := (Finset.mem_Icc.1 hs).2
        have h1 : (2 : ℝ) ^ s ≤ 2 ^ Sm := pow_le_pow_right₀ (by norm_num) (hs2.trans hSm)
        have h2 : (((wordCount α).1 + 1) * ((wordCount α).2 + 1) : ℕ) ≤ (Dm + 1) ^ 2 := by
          have : (wordCount α).1 + 1 ≤ Dm + 1 := by omega
          have h' : (wordCount α).2 + 1 ≤ Dm + 1 := by omega
          calc _ ≤ (Dm + 1) * (Dm + 1) := Nat.mul_le_mul this h'
            _ = _ := by ring
        have h2' : ((((wordCount α).1 + 1) * ((wordCount α).2 + 1) : ℕ) : ℝ) ≤ ((Dm : ℝ) + 1) ^ 2 := by
          exact_mod_cast h2
        push_cast at h2' ⊢
        have hW : 0 ≤ X * Jet α s := mul_nonneg hX hP
        calc _ ≤ (2 : ℝ) ^ Sm * (((Dm : ℝ) + 1) ^ 2 * (X * Jet α s)) :=
              mul_le_mul h1 (mul_le_mul_of_nonneg_right h2' hW) (by positivity) (by positivity)
          _ = _ := by ring
    _ ≤ ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range (slow + 1),
        (2 : ℝ) ^ Sm * ((Dm : ℝ) + 1) ^ 2 * X * Jet α s := by
        refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun s _ _ => mul_nonneg (by positivity) (hJ α s))
        intro s hs
        obtain ⟨-, h2⟩ := Finset.mem_Icc.1 hs
        exact Finset.mem_range.2 (by omega)
    _ = _ := by
        simp only [← Finset.mul_sum]

theorem sgU1_zero (ρ : ℝ) (n : ℕ) (pre : Bool) (p q : ℕ) (Jt : ℝ) :
    sgU1 ρ n pre p q Jt 0 = 0 := by simp [sgU1]

theorem sgU2_zero (θ : Vec 2) (ρ : ℝ) (n : ℕ) (pre : Bool) (p q : ℕ) (Jt : ℝ) :
    sgU2 θ ρ n pre p q Jt 0 = 0 := by simp [sgU2]

theorem sgU3_zero (θ : Vec 2) (ρ : ℝ) (n : ℕ) (pre : Bool) (k : Fin 2) (kc : ℝ) (p q : ℕ)
    (Jt : ℝ) : sgU3 θ ρ n pre k kc p q Jt 0 = 0 := by simp [sgU3]

theorem sgU4_zero (θ : Vec 2) (n : ℕ) (pre : Bool) (k : Fin 2) (kc : ℝ) (p q : ℕ)
    (Jt : ℝ) : sgU4 θ n pre k kc p q Jt 0 = 0 := by simp [sgU4]

/-- Common facts of a unit term: the scalar bound with the exact power of `ϖ`. -/
theorem gain_sum
    {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] {D Nw : ℕ} (π : ι → ℝ) (ϖ ηg : ℝ)
    (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw) (x x' : ι) (β β' β₀ : ℕ × ℕ)
    (d M0 Dm n Sm : ℕ) (hSm : (letters l).slow ≤ Sm) (ρ : ℝ) (hρ : 0 ≤ ρ) (pre : Bool) (k : Fin 2)
    (cv : ℝ) (hcv : |cv| ≤ (M0 : ℝ) + 1)
    (hx : 0 < π x) (hx' : 0 < π x') (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1)
    (hθ : 0 < (letters l).theta) (hd : d ≤ Dm) (hd2 : 2 ≤ d) (hb0 : β₀.1 + β₀.2 ≤ β.1 + β.2)
    (hβM : β.1 + β.2 ≤ M0) (hβ'M : β'.1 + β'.2 ≤ M0)
    (hlow : pre = false → cv ≠ 0 → β₀.1 + β₀.2 + 1 = β.1 + β.2)
    (ζ t : ℝ) (hϖζ : ϖ ≤ ζ) (hζ1 : ζ ≤ 1) (ht0 : 0 ≤ t) (htζ : t ≤ (1 + ρ) * ζ)
    (θ : Vec 2) (hθt : ∀ j, |θ j| ≤ t) (kc : ℝ) (hkc : 0 ≤ kc)
    (Jet : DerivativeWord2 (d - 1) → ℕ → ℝ) (hJ : ∀ α s, 0 ≤ Jet α s)
    :
    sgSum (letters l).positive (letters l).slow d (fun α s w a => sgU1 ρ n pre
        ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s)
        (sgKap (slSel true β β₀) (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s
          (wordCount α).1 (wordCount α).2 β₀ w a β')) ≤
      ϖ * (gamCfin Dm n ρ M0 Sm * (Real.sqrt (π x' / π x) / (letters l).theta) *
        ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range ((letters l).slow + 1), Jet α s) ∧
    sgSum (letters l).positive (letters l).slow d (fun α s w a => sgU4 θ n pre k kc
        ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s)
        (sgKap (slSel true β β₀) (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s
          (wordCount α).1 (wordCount α).2 β₀ w a β')) ≤
      ζ ^ 2 * kc * (gamCfin Dm n ρ M0 Sm * (Real.sqrt (π x' / π x) / (letters l).theta) *
        ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range ((letters l).slow + 1), Jet α s) := by
  classical
  have hCc := gamCc_nonneg Dm M0 Sm
  have hsq : 0 ≤ Real.sqrt (π x' / π x) / (letters l).theta := by positivity
  have hPr0 : 0 ≤ gamPr n Dm := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set c0 := gamCc Dm M0 Sm * (Real.sqrt (π x' / π x) / (letters l).theta) with hc0def
  have hc0 : 0 ≤ c0 := by positivity
  have hζ0 : 0 ≤ ζ := hϖ0.le.trans hϖζ
  -- the unit facts
  have unit : ∀ α : DerivativeWord2 (d - 1), ∀ s, s ∈ Finset.Icc (if (letters l).positive then 1 else 0)
      (letters l).slow → ∀ ω : DerivativeWord2 s, ∀ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
        Finset.range ((wordCount α).2 + 1),
      sgU1 ρ n pre ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s)
        (sgKap (slSel true β β₀) (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s
          (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β') ≤
        (ϖ * (c0 * ((1 + ρ) ^ Dm * gamPr n Dm))) * Jet α s ∧
      sgU4 θ n pre k kc ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s)
        (sgKap (slSel true β β₀) (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s
          (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β') ≤
        (ζ ^ 2 * kc * (c0 * ((1 + ρ) ^ Dm * gamPr n Dm))) * Jet α s := by
    intro α s hs ω a ha
    obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
    have hwa := wordCount_sum α
    have hwo := wordCount_sum ω
    obtain ⟨ha1, ha2⟩ := Finset.mem_product.1 ha
    have ha1' := Finset.mem_range.1 ha1
    have ha2' := Finset.mem_range.1 ha2
    have hJs := hJ α s
    have hpr : |cellDriftNativePrice (n + ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2))| ≤
        gamPr n Dm :=
      Finset.single_le_sum (f := fun K => |cellDriftNativePrice K|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    have hκ := kap_le (slSel true β β₀) π ϖ ηg letters l x x' β β' β₀ (wordCount ω) a s d
      (wordCount α).1 (wordCount α).2 M0 Sm Dm cv hcv hx hx' hϖ0 hϖ1 hg0 hg1 hθ hs1
      (hs2.trans hSm) hwo hb0 hβM hβ'M (by omega) (by omega) (by omega) (by omega)
    rw [← hc0def] at hκ
    by_cases hP : slSel true β β₀ a
    · have hE : 1 ≤ β.1 + β.2 - (β₀.1 + β₀.2) + (a.1 + a.2) := by simpa [slSel] using hP
      by_cases hc : cv = 0
      · have hk0 : sgKap (slSel true β β₀) (letterRatioReal π ϖ ηg letters l x x' β β' * cv)
            (ϖ * ηg) d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β' = 0 := by
          rw [hc]; exact kap_zero _ _ _ _ _ _ _ _ _ _ _
        rw [hk0, sgU1_zero, sgU4_zero]
        constructor <;> positivity
      · have hEm : 2 ≤ β.1 + β.2 - (β₀.1 + β₀.2) + (a.1 + a.2) ∨
            1 ≤ ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2) + preExp pre := by
          cases pre
          · have := hlow rfl hc
            simp only [preExp, Bool.false_eq_true, ite_false]
            omega
          · simp only [preExp, ite_true]; omega
        have hpq : ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2) + preExp pre ≤ Dm := by
          cases pre <;> simp only [preExp, Bool.false_eq_true, ite_false, ite_true] <;> omega
        refine ⟨?_, ?_⟩
        · have := gain_u1 (n := n) (Dm := Dm) (p := (wordCount α).1 - a.1)
            (q := (wordCount α).2 - a.2) (pre := pre) hρ hϖ0.le hϖ1 hc0 hJs _ hE hκ hpq hpr
          calc _ ≤ _ := this
            _ = _ := by ring
        · have := gain_u4 (n := n) (Dm := Dm) (p := (wordCount α).1 - a.1)
            (q := (wordCount α).2 - a.2) (pre := pre) (k := k) hρ hϖ0.le hϖζ hζ1 ht0 htζ hθt hc0 hJs
            hkc _ hE hEm hκ hpq hpr
          calc _ ≤ _ := this
            _ = _ := by ring
    · rw [kap_of_not _ _ _ _ _ _ _ _ _ _ _ hP, sgU1_zero, sgU4_zero]
      constructor <;> positivity
  have hX1 : 0 ≤ ϖ * (c0 * ((1 + ρ) ^ Dm * gamPr n Dm)) := by positivity
  have hX4 : 0 ≤ ζ ^ 2 * kc * (c0 * ((1 + ρ) ^ Dm * gamPr n Dm)) := by positivity
  have e : ∀ X : ℝ, (2 : ℝ) ^ Sm * ((Dm : ℝ) + 1) ^ 2 * (X * (c0 * ((1 + ρ) ^ Dm * gamPr n Dm))) *
      (∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range ((letters l).slow + 1), Jet α s) =
      X * (gamCfin Dm n ρ M0 Sm * (Real.sqrt (π x' / π x) / (letters l).theta) *
        ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range ((letters l).slow + 1), Jet α s) := by
    intro X
    unfold gamCfin
    rw [hc0def]
    ring
  refine ⟨?_, ?_⟩
  · refine (sgSum_le _ _ Sm d Dm hd hSm _ Jet _ hX1 hJ (fun α s hs ω a ha => (unit α s hs ω a ha).1)).trans ?_
    exact le_of_eq (e ϖ)
  · refine (sgSum_le _ _ Sm d Dm hd hSm _ Jet _ hX4 hJ (fun α s hs ω a ha => (unit α s hs ω a ha).2)).trans ?_
    exact le_of_eq (e (ζ ^ 2 * kc))

theorem zero_u1 {ρ : ℝ} {n Dm p q : ℕ} {Jt κ c0 Pr : ℝ} (hρ : 0 ≤ ρ) (hc0 : 0 ≤ c0)
    (hJ : 0 ≤ Jt) (hκ : |κ| ≤ c0) (hpq : p + q + 1 ≤ Dm)
    (hPr : |cellDriftNativePrice (n + p + q)| ≤ Pr) :
    sgU1 ρ n true p q Jt κ ≤ 1 * (c0 * ((1 + ρ) ^ Dm * Pr) * Jt) := by
  have hPr0 : 0 ≤ Pr := (abs_nonneg _).trans hPr
  have h2 : (1 + ρ) ^ (p + q + preExp true) ≤ (1 + ρ) ^ Dm :=
    pow_le_pow_right₀ (by linarith) (by simpa [preExp] using hpq)
  unfold sgU1
  calc _ ≤ c0 * ((1 + ρ) ^ Dm * (Pr * Jt)) := by gcongr
    _ = _ := by ring

theorem zero_sum
    {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] {D Nw : ℕ} (π : ι → ℝ) (ϖ ηg : ℝ)
    (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw) (x x' : ι) (β β' β₀ : ℕ × ℕ)
    (d M0 Dm n Sm : ℕ) (hSm : (letters l).slow ≤ Sm) (ρ : ℝ) (hρ : 0 ≤ ρ) (pre : Bool) (k : Fin 2)
    (cv : ℝ) (hcv : |cv| ≤ (M0 : ℝ) + 1)
    (hx : 0 < π x) (hx' : 0 < π x') (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1)
    (hθ : 0 < (letters l).theta) (hd : d ≤ Dm) (hd2 : 2 ≤ d) (hb0 : β₀.1 + β₀.2 ≤ β.1 + β.2)
    (hβM : β.1 + β.2 ≤ M0) (hβ'M : β'.1 + β'.2 ≤ M0)
    (hlow : pre = false → cv ≠ 0 → β₀.1 + β₀.2 + 1 = β.1 + β.2)
    (ζ t : ℝ) (hϖζ : ϖ ≤ ζ) (hζ1 : ζ ≤ 1) (ht0 : 0 ≤ t) (htρ : t ≤ ρ) (htζ : t ≤ (1 + ρ) * ζ)
    (θ : Vec 2) (hθt : ∀ j, |θ j| ≤ t) (kc : ℝ) (hkc : 0 ≤ kc)
    (Jet : DerivativeWord2 (d - 1) → ℕ → ℝ) (hJ : ∀ α s, 0 ≤ Jet α s) :
    sgSum (letters l).positive (letters l).slow d (fun α s w a => sgU1 ρ n pre
        ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s)
        (sgKap (slSel false β β₀) (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s
          (wordCount α).1 (wordCount α).2 β₀ w a β')) ≤
      1 * (gamCfin Dm n ρ M0 Sm * (Real.sqrt (π x' / π x) / (letters l).theta) *
        ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range ((letters l).slow + 1), Jet α s) ∧
    sgSum (letters l).positive (letters l).slow d (fun α s w a => sgU2 θ ρ n pre
        ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s)
        (sgKap (slSel false β β₀) (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s
          (wordCount α).1 (wordCount α).2 β₀ w a β')) ≤
      t * (gamCfin Dm n ρ M0 Sm * (Real.sqrt (π x' / π x) / (letters l).theta) *
        ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range ((letters l).slow + 1), Jet α s) ∧
    sgSum (letters l).positive (letters l).slow d (fun α s w a => sgU3 θ ρ n pre k kc
        ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s)
        (sgKap (slSel false β β₀) (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s
          (wordCount α).1 (wordCount α).2 β₀ w a β')) ≤
      t * kc * (gamCfin Dm n ρ M0 Sm * (Real.sqrt (π x' / π x) / (letters l).theta) *
        ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range ((letters l).slow + 1), Jet α s) ∧
    sgSum (letters l).positive (letters l).slow d (fun α s w a => sgU4 θ n pre k kc
        ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s)
        (sgKap (slSel false β β₀) (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s
          (wordCount α).1 (wordCount α).2 β₀ w a β')) ≤
      ζ ^ 2 * kc * (gamCfin Dm n ρ M0 Sm * (Real.sqrt (π x' / π x) / (letters l).theta) *
        ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range ((letters l).slow + 1), Jet α s) := by
  classical
  have hCc := gamCc_nonneg Dm M0 Sm
  have hsq : 0 ≤ Real.sqrt (π x' / π x) / (letters l).theta := by positivity
  have hPr0 : 0 ≤ gamPr n Dm := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set c0 := gamCc Dm M0 Sm * (Real.sqrt (π x' / π x) / (letters l).theta) with hc0def
  have hc0 : 0 ≤ c0 := by positivity
  have hζ0 : 0 ≤ ζ := hϖ0.le.trans hϖζ
  have unit : ∀ α : DerivativeWord2 (d - 1), ∀ s, s ∈ Finset.Icc (if (letters l).positive then 1 else 0)
      (letters l).slow → ∀ ω : DerivativeWord2 s, ∀ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
        Finset.range ((wordCount α).2 + 1),
      sgU1 ρ n pre ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s)
        (sgKap (slSel false β β₀) (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s
          (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β') ≤
        (1 * (c0 * ((1 + ρ) ^ Dm * gamPr n Dm))) * Jet α s ∧
      sgU2 θ ρ n pre ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s)
        (sgKap (slSel false β β₀) (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s
          (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β') ≤
        (t * (c0 * ((1 + ρ) ^ Dm * gamPr n Dm))) * Jet α s ∧
      sgU3 θ ρ n pre k kc ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s)
        (sgKap (slSel false β β₀) (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s
          (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β') ≤
        (t * kc * (c0 * ((1 + ρ) ^ Dm * gamPr n Dm))) * Jet α s ∧
      sgU4 θ n pre k kc ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s)
        (sgKap (slSel false β β₀) (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s
          (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β') ≤
        (ζ ^ 2 * kc * (c0 * ((1 + ρ) ^ Dm * gamPr n Dm))) * Jet α s := by
    intro α s hs ω a ha
    obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
    have hwa := wordCount_sum α
    have hwo := wordCount_sum ω
    obtain ⟨ha1, ha2⟩ := Finset.mem_product.1 ha
    have ha1' := Finset.mem_range.1 ha1
    have ha2' := Finset.mem_range.1 ha2
    have hJs := hJ α s
    have hpr : |cellDriftNativePrice (n + ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2))| ≤
        gamPr n Dm :=
      Finset.single_le_sum (f := fun K => |cellDriftNativePrice K|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    have hκ := kap_le (slSel false β β₀) π ϖ ηg letters l x x' β β' β₀ (wordCount ω) a s d
      (wordCount α).1 (wordCount α).2 M0 Sm Dm cv hcv hx hx' hϖ0 hϖ1 hg0 hg1 hθ hs1
      (hs2.trans hSm) hwo hb0 hβM hβ'M (by omega) (by omega) (by omega) (by omega)
    rw [← hc0def] at hκ
    have hall0 : ∀ κ : ℝ, κ = 0 →
        sgU1 ρ n pre ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s) κ ≤
          (1 * (c0 * ((1 + ρ) ^ Dm * gamPr n Dm))) * Jet α s ∧
        sgU2 θ ρ n pre ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s) κ ≤
          (t * (c0 * ((1 + ρ) ^ Dm * gamPr n Dm))) * Jet α s ∧
        sgU3 θ ρ n pre k kc ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s) κ ≤
          (t * kc * (c0 * ((1 + ρ) ^ Dm * gamPr n Dm))) * Jet α s ∧
        sgU4 θ n pre k kc ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) (Jet α s) κ ≤
          (ζ ^ 2 * kc * (c0 * ((1 + ρ) ^ Dm * gamPr n Dm))) * Jet α s := by
      intro κ hk
      subst hk
      rw [sgU1_zero, sgU2_zero, sgU3_zero, sgU4_zero]
      exact ⟨by positivity, by positivity, by positivity, by positivity⟩
    by_cases hP : slSel false β β₀ a
    · have hE0 : β.1 + β.2 - (β₀.1 + β₀.2) + (a.1 + a.2) = 0 := by simpa [slSel] using hP
      by_cases hc : cv = 0
      · refine hall0 _ ?_
        rw [hc]; exact kap_zero _ _ _ _ _ _ _ _ _ _ _
      · have hpt : pre = true := by
          by_contra hne
          have hpf : pre = false := by simpa using hne
          have := hlow hpf hc
          omega
        subst hpt
        rw [hE0, pow_zero, one_mul] at hκ
        have ha0 : a = (0, 0) := by
          exact Prod.ext (by show a.1 = 0; omega) (by show a.2 = 0; omega)
        subst ha0
        have hpq1 : 1 ≤ ((wordCount α).1 - 0) + ((wordCount α).2 - 0) := by omega
        have hpq : ((wordCount α).1 - 0) + ((wordCount α).2 - 0) + 1 ≤ Dm := by omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact (zero_u1 hρ hc0 hJs hκ hpq hpr).trans (le_of_eq (by ring))
        · exact (zero_u2 hρ ht0 htρ hθt hc0 hJs hκ hpq1 hpq hpr).trans (le_of_eq (by ring))
        · exact (zero_u3 hρ hθt hc0 hJs hkc hκ (le_trans (Nat.le_succ _) hpq) hpr).trans (le_of_eq (by ring))
        · exact (zero_u4 hρ hζ0 hζ1 ht0 htζ hθt hc0 hJs hkc hκ hpq1 hpq hpr).trans
            (le_of_eq (by ring))
    · exact hall0 _ (kap_of_not _ _ _ _ _ _ _ _ _ _ _ hP)
  have e : ∀ X : ℝ, (2 : ℝ) ^ Sm * ((Dm : ℝ) + 1) ^ 2 * (X * (c0 * ((1 + ρ) ^ Dm * gamPr n Dm))) *
      (∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range ((letters l).slow + 1), Jet α s) =
      X * (gamCfin Dm n ρ M0 Sm * (Real.sqrt (π x' / π x) / (letters l).theta) *
        ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range ((letters l).slow + 1), Jet α s) := by
    intro X
    unfold gamCfin
    rw [hc0def]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (sgSum_le _ _ Sm d Dm hd hSm _ Jet _ (by positivity) hJ
      (fun α s hs ω a ha => (unit α s hs ω a ha).1)).trans ?_
    exact le_of_eq (e 1)
  · refine (sgSum_le _ _ Sm d Dm hd hSm _ Jet _ (by positivity) hJ
      (fun α s hs ω a ha => (unit α s hs ω a ha).2.1)).trans ?_
    exact le_of_eq (e t)
  · refine (sgSum_le _ _ Sm d Dm hd hSm _ Jet _ (by positivity) hJ
      (fun α s hs ω a ha => (unit α s hs ω a ha).2.2.1)).trans ?_
    exact le_of_eq (e (t * kc))
  · refine (sgSum_le _ _ Sm d Dm hd hSm _ Jet _ (by positivity) hJ
      (fun α s hs ω a ha => (unit α s hs ω a ha).2.2.2)).trans ?_
    exact le_of_eq (e (ζ ^ 2 * kc))

end AVRegularity.CycleWords.Assembly
end
