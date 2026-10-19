-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.BoxJoint
import Mathlib.Topology.Compactness.DeltaGeneratedSpace

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Providers.GenSem

/-! Scalar coefficient arrays for applied fields, basics.

`CArr` is a coefficient array at fixed time. `applyArr K A a` is the applied field
`(X,z) ↦ ∑_{m ≤ K} ∑_{|α| = m} A m α X z * ∂^α a (X)`. This file has the word calculus
(`orderedDerivative` of `Fin.snoc`), smoothness of ordered derivatives, and the linear algebra
(sums, scalar multiples, products with functions, cell mean, evaluation on monomials). -/

/-- A scalar coefficient array at fixed time. -/
abbrev CArr : Type := (m : ℕ) → DerivativeWord2 m → Vec 2 → Vec 2 → ℝ

/-- The applied field `(X,z) ↦ ∑_{m ≤ K} ∑_{|α|=m} A m α X z * ∂^α a(X)`. -/
def applyArr (K : ℕ) (A : CArr) (a : Vec 2 → ℝ) : Vec 2 → Vec 2 → ℝ :=
  fun X z => ∑ m ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 m,
    A m α X z * orderedDerivative α a X

/-- The array vanishes above order `K`. -/
def ArrSupp (K : ℕ) (A : CArr) : Prop := ∀ m, K < m → ∀ α, A m α = 0

/-! ### Word calculus -/

theorem orderedDerivative_snoc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (α : DerivativeWord2 m) (i : Fin 2) (g : Vec 2 → E) :
    orderedDerivative (Fin.snoc α i : DerivativeWord2 (m + 1)) g =
      fun x => fderiv ℝ (orderedDerivative α g) x (basisVec i) := by
  unfold orderedDerivative
  rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
  simp

/-- One directional derivative costs one order of smoothness. -/
theorem contDiff_dirDeriv_nat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Vec 2 → E}
    {r : ℕ} (hg : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) g) (i : Fin 2) :
    ContDiff ℝ (r : WithTop ℕ∞) (fun x => fderiv ℝ g x (basisVec i)) := by
  have h := hg.fderiv_right (m := (r : WithTop ℕ∞)) (by push_cast; exact le_rfl)
  exact h.clm_apply contDiff_const

/-- An ordered derivative of order `m` costs `m` orders of smoothness. -/
theorem contDiff_orderedDerivative_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r m : ℕ} (α : DerivativeWord2 m) {g : Vec 2 → E}
    (hg : ContDiff ℝ ((r + m : ℕ) : WithTop ℕ∞) g) :
    ContDiff ℝ (r : WithTop ℕ∞) (orderedDerivative α g) := by
  induction m generalizing g with
  | zero =>
    have : α = Fin.elim0 := Subsingleton.elim _ _
    subst this
    rwa [orderedDerivative_zero_word]
  | succ m ih =>
    rw [orderedDerivative_succ]
    exact ih _ (contDiff_dirDeriv_nat (r := r + m) hg _)

/-! ### Linear algebra -/

theorem applyArr_add (K : ℕ) (A B : CArr) (a : Vec 2 → ℝ) :
    applyArr K (A + B) a = applyArr K A a + applyArr K B a := by
  funext X z
  simp only [applyArr, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem applyArr_smul (K : ℕ) (c : ℝ) (A : CArr) (a : Vec 2 → ℝ) :
    applyArr K (c • A) a = c • applyArr K A a := by
  funext X z
  simp only [applyArr, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem applyArr_zero (K : ℕ) (a : Vec 2 → ℝ) : applyArr K 0 a = 0 := by
  funext X z
  simp [applyArr]

theorem applyArr_sum {ι : Type*} (s : Finset ι) (K : ℕ) (A : ι → CArr) (a : Vec 2 → ℝ) :
    applyArr K (∑ i ∈ s, A i) a = ∑ i ∈ s, applyArr K (A i) a := by
  funext X z
  simp only [applyArr, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]

/-- Multiplication of all coefficients by a function of `(X,z)`. -/
def mulArr (g : Vec 2 → Vec 2 → ℝ) (A : CArr) : CArr :=
  fun m α X z => g X z * A m α X z

theorem applyArr_mulArr (K : ℕ) (g : Vec 2 → Vec 2 → ℝ) (A : CArr) (a : Vec 2 → ℝ) :
    applyArr K (mulArr g A) a = fun X z => g X z * applyArr K A a X z := by
  funext X z
  simp only [applyArr, mulArr, Finset.mul_sum, mul_assoc]

/-- The cell mean of each coefficient (constant in `z`). -/
def meanArr (A : CArr) : CArr :=
  fun m α X _ => fieldCellMean (fun z' => A m α X z')

/-- Cell mean of an applied field, `a` being independent of `z`. Hypothesis: each coefficient is
integrable over the unit cube in `z`. -/
theorem fieldCellMean_applyArr (K : ℕ) (A : CArr) (a : Vec 2 → ℝ) (X z0 : Vec 2)
    (hA : ∀ m α, IntegrableOn (fun z => A m α X z) AVenhance.unitCube) :
    fieldCellMean (fun z => applyArr K A a X z) = applyArr K (meanArr A) a X z0 := by
  unfold fieldCellMean applyArr meanArr
  rw [integral_finsetSum _ (fun m _ => integrable_finsetSum _
    (fun α _ => (hA m α).mul_const _))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ (fun α _ => (hA m α).mul_const _)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_mul_const]; rfl

/-! ### Support, truncation -/

theorem applyArr_eq_of_supp {K K' : ℕ} (hK : K ≤ K') {A : CArr} (hA : ArrSupp K A)
    (a : Vec 2 → ℝ) : applyArr K' A a = applyArr K A a := by
  funext X z
  unfold applyArr
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun m hm hm' => ?_
  have : K < m := by simp at hm hm'; omega
  simp [hA m this]

/-! ### Evaluation at the centre -/

theorem applyArr_mono (K : ℕ) (A : CArr) (y z : Vec 2) {m : ℕ} (I : DerivativeWord2 m)
    (hm : m ≤ K) :
    applyArr K A (mono y I) y z = ∑ σ : Equiv.Perm (Fin m), A m (I ∘ σ) y z := by
  unfold applyArr
  rw [Finset.sum_eq_single m]
  · have := sum_orderedDerivative_mono y I (fun α => A m α y z)
    simp only [smul_eq_mul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  · intro m' _ hm'
    exact Finset.sum_eq_zero fun α _ => by
      rw [orderedDerivative_mono_of_ne y I α hm', mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-! Slow and fast partial derivatives of applied fields.

Letter convention: `orderedDerivative α g = ∂_{α_{m-1}}(⋯ ∂_{α_0} g)`, so the last letter
`β (Fin.last m)` of a word is the outermost derivative and `∂_j (∂^α a) = ∂^{Fin.snoc α j} a`. -/

/-- Each coefficient is `C^r` in the slow variable `X`, `z` fixed. -/
def ArrSlowSmooth (r : ℕ) (A : CArr) : Prop :=
  ∀ m α z, ContDiff ℝ (r : WithTop ℕ∞) (fun X => A m α X z)

theorem ArrSlowSmooth.mono {r r' : ℕ} (h : r' ≤ r) {A : CArr} (hA : ArrSlowSmooth r A) :
    ArrSlowSmooth r' A :=
  fun m α z => (hA m α z).of_le (by exact_mod_cast h)

/-- The extra coefficient created by differentiating `∂^α a`: the word `β` of order `m+1` whose
last letter is `j` receives `A m (init β)`. -/
def slowExtra (j : Fin 2) (A : CArr) : CArr
  | 0, _, _, _ => 0
  | m + 1, β, X, z => if β (Fin.last m) = j then A m (Fin.init β) X z else 0

/-- The array of `∂_{X_j}` of an applied field. -/
def slowArr (j : Fin 2) (A : CArr) : CArr :=
  fun m β X z => slowPartial j (A m β) X z + slowExtra j A m β X z

/-- Iterated slow arrays along a word (letters `α 0, α 1, …` in this order). -/
def iterSlow : (n : ℕ) → DerivativeWord2 n → CArr → CArr
  | 0, _, B => B
  | n + 1, α, B => iterSlow n (fun i => α i.succ) (slowArr (α 0) B)

theorem arrSupp_slowArr {K : ℕ} {A : CArr} (j : Fin 2) (hA : ArrSupp K A) :
    ArrSupp (K + 1) (slowArr j A) := by
  intro m hm β
  funext X z
  have h0 : slowPartial j (A m β) X z = 0 := by
    rw [hA m (by omega) β]; simp [slowPartial]
  cases m with
  | zero => omega
  | succ m =>
    have : A m = 0 := funext fun α => hA m (by omega) α
    simp only [slowArr, h0, slowExtra, this, Pi.zero_apply, ite_self, add_zero]

theorem arrSlowSmooth_slowArr {r : ℕ} {A : CArr} (j : Fin 2) (hA : ArrSlowSmooth (r + 1) A) :
    ArrSlowSmooth r (slowArr j A) := by
  intro m β z
  have h1 : ContDiff ℝ (r : WithTop ℕ∞) (fun X => slowPartial j (A m β) X z) :=
    contDiff_dirDeriv_nat (hA m β z) j
  cases m with
  | zero => simpa [slowArr, slowExtra] using h1
  | succ m =>
    simp only [slowArr, slowExtra]
    split_ifs
    · exact h1.add ((hA.mono (Nat.le_succ r)) m _ z)
    · simpa using h1

theorem arrSupp_iterSlow {K : ℕ} : ∀ {n : ℕ} (α : DerivativeWord2 n) {B : CArr},
    ArrSupp K B → ArrSupp (K + n) (iterSlow n α B) := by
  intro n
  induction n generalizing K with
  | zero => intro α B h; simpa [iterSlow] using h
  | succ n ih =>
    intro α B h
    have := ih (K := K + 1) (fun i => α i.succ) (arrSupp_slowArr (α 0) h)
    rwa [show K + 1 + n = K + (n + 1) by omega] at this

theorem arrSlowSmooth_iterSlow {r : ℕ} : ∀ {n : ℕ} (α : DerivativeWord2 n) {B : CArr},
    ArrSlowSmooth (r + n) B → ArrSlowSmooth r (iterSlow n α B) := by
  intro n
  induction n with
  | zero => intro α B h; simpa [iterSlow] using h
  | succ n ih =>
    intro α B h
    exact ih (fun i => α i.succ) (arrSlowSmooth_slowArr (α 0) h)

/-- Reindexing of the extra coefficients through `Fin.snoc`. -/
theorem sum_slowExtra (j : Fin 2) (A : CArr) (m : ℕ) (X z : Vec 2)
    (G : DerivativeWord2 (m + 1) → ℝ) :
    ∑ β : DerivativeWord2 (m + 1), slowExtra j A (m + 1) β X z * G β =
      ∑ α : DerivativeWord2 m, A m α X z * G (Fin.snoc α j) := by
  classical
  rw [← (Fin.snocEquiv (fun _ : Fin (m + 1) => Fin 2)).sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · refine Finset.sum_congr rfl fun α _ => ?_
    have e : (Fin.snocEquiv (fun _ : Fin (m + 1) => Fin 2)) (j, α) = Fin.snoc α j := rfl
    simp [e, slowExtra]
  · intro i _ hij
    refine Finset.sum_eq_zero fun α _ => ?_
    have e : (Fin.snocEquiv (fun _ : Fin (m + 1) => Fin 2)) (i, α) = Fin.snoc α i := rfl
    simp [e, slowExtra, hij]
  · simp

theorem orderedDerivative_differentiable {m : ℕ} (α : DerivativeWord2 m) {a : Vec 2 → ℝ}
    (ha : ContDiff ℝ ((1 + m : ℕ) : WithTop ℕ∞) a) : Differentiable ℝ (orderedDerivative α a) :=
  (contDiff_orderedDerivative_top (r := 1) α ha).differentiable (by simp)

/-- Slow derivative of an applied field is an applied field one order higher. -/
theorem slowPartial_applyArr (K : ℕ) (A : CArr) (a : Vec 2 → ℝ) (j : Fin 2)
    (ha : ContDiff ℝ ((K + 1 : ℕ) : WithTop ℕ∞) a) (hA : ArrSlowSmooth 1 A) (hs : ArrSupp K A) :
    slowPartial j (applyArr K A a) = applyArr (K + 1) (slowArr j A) a := by
  funext X z
  have key : ∀ m ∈ Finset.range (K + 1), ∀ (α : DerivativeWord2 m),
      HasFDerivAt (fun X' => A m α X' z * orderedDerivative α a X')
        (A m α X z • fderiv ℝ (orderedDerivative α a) X +
          orderedDerivative α a X • fderiv ℝ (fun X' => A m α X' z) X) X := fun m hm α =>
    ((hA m α z).differentiable (by simp) X).hasFDerivAt.mul
      ((orderedDerivative_differentiable α
        (ha.of_le (by
          have : m ≤ K := by simpa [Nat.lt_succ_iff] using hm
          exact_mod_cast (by omega : 1 + m ≤ K + 1)))) X).hasFDerivAt
  have h := HasFDerivAt.fun_sum (u := Finset.range (K + 1))
    (fun m hm => HasFDerivAt.fun_sum (u := (Finset.univ : Finset (DerivativeWord2 m)))
      (fun α _ => key m hm α))
  unfold slowPartial applyArr
  rw [h.fderiv]
  simp only [sum_apply, add_apply, smul_apply, smul_eq_mul, slowArr, add_mul,
    Finset.sum_add_distrib]
  have hE : ∑ x ∈ Finset.range (K + 1 + 1), ∑ β : DerivativeWord2 x,
      slowExtra j A x β X z * orderedDerivative β a X =
      ∑ x ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 x,
        A x α X z * (fderiv ℝ (orderedDerivative α a) X) (basisVec j) := by
    rw [Finset.sum_range_succ']
    have h0 : ∀ β : DerivativeWord2 0, slowExtra j A 0 β X z = 0 := fun _ => rfl
    simp only [h0, Finset.sum_const_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [sum_slowExtra j A m X z (fun β => orderedDerivative β a X)]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [orderedDerivative_snoc]
  have hP : ∑ x ∈ Finset.range (K + 1 + 1), ∑ β : DerivativeWord2 x,
      slowPartial j (A x β) X z * orderedDerivative β a X =
      ∑ x ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 x,
        orderedDerivative α a X * (fderiv ℝ (fun X' => A x α X' z) X) (basisVec j) := by
    rw [Finset.sum_range_succ]
    have : ∀ β : DerivativeWord2 (K + 1),
        slowPartial j (A (K + 1) β) X z * orderedDerivative β a X = 0 := fun β => by
      rw [hs (K + 1) (by omega) β]; simp [slowPartial]
    simp only [this, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun α _ => ?_
    rw [mul_comm]; rfl
  rw [hE, hP, add_comm]

/-! Fast derivatives, ordered derivatives of applied fields, and composition. -/

/-- The fast partial of an applied field: `∂_{z_j}` acts on the coefficients only. Hypothesis:
each coefficient is differentiable in `z`, `X` fixed. -/
theorem fastPartial_applyArr (K : ℕ) (A : CArr) (a : Vec 2 → ℝ) (j : Fin 2)
    (hA : ∀ m α X, Differentiable ℝ (fun z => A m α X z)) :
    fastPartial j (applyArr K A a) = applyArr K (fun m α => fastPartial j (A m α)) a := by
  funext X z
  have key : ∀ m (α : DerivativeWord2 m),
      HasFDerivAt (fun z' => A m α X z' * orderedDerivative α a X)
        (orderedDerivative α a X • fderiv ℝ (fun z' => A m α X z') z) z :=
    fun m α => ((hA m α X) z).hasFDerivAt.mul_const _
  have h := HasFDerivAt.fun_sum (u := Finset.range (K + 1))
    (fun m _ => HasFDerivAt.fun_sum (u := (Finset.univ : Finset (DerivativeWord2 m)))
      (fun α _ => key m α))
  unfold fastPartial applyArr
  rw [h.fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun α _ => ?_
  rw [mul_comm]

/-- The ordered derivative of an applied field is an applied field of `|α|` orders higher. -/
theorem orderedDerivative_applyArr : ∀ {n : ℕ} (α : DerivativeWord2 n) (K : ℕ) (B : CArr)
    (a : Vec 2 → ℝ) (z : Vec 2), ContDiff ℝ ((K + n : ℕ) : WithTop ℕ∞) a → ArrSlowSmooth n B →
    ArrSupp K B →
    orderedDerivative α (fun X => applyArr K B a X z) =
      fun X => applyArr (K + n) (iterSlow n α B) a X z := by
  intro n
  induction n with
  | zero =>
    intro α K B a z _ _ _
    have : α = Fin.elim0 := Subsingleton.elim _ _
    subst this
    rw [orderedDerivative_zero_word]
    rfl
  | succ n ih =>
    intro α K B a z ha hB hs
    rw [orderedDerivative_succ]
    have h1 : (fun x => fderiv ℝ (fun X => applyArr K B a X z) x (basisVec (α 0))) =
        fun X => applyArr (K + 1) (slowArr (α 0) B) a X z := by
      funext X
      exact congrFun (congrFun (slowPartial_applyArr K B a (α 0)
        (ha.of_le (by exact_mod_cast (by omega : K + 1 ≤ K + (n + 1)))) (hB.mono (by omega)) hs) X) z
    have ha' : ContDiff ℝ ((K + 1 + n : ℕ) : WithTop ℕ∞) a := by
      rwa [show K + 1 + n = K + (n + 1) by omega]
    rw [h1, ih (fun i => α i.succ) (K + 1) _ a z ha' (arrSlowSmooth_slowArr (r := n) _ hB)
      (arrSupp_slowArr _ hs)]
    rw [show K + 1 + n = K + (n + 1) by omega]
    rfl

/-- The coefficient array of `applyArr J C` applied to the field `X ↦ applyArr K B a X z0`:
`∑_{m ≤ J} ∑_{|α| = m} C m α X z * (∂_X^α-slow array of B)(·,z0)`. -/
def compArr (J : ℕ) (C B : CArr) (z0 : Vec 2) : CArr :=
  fun m' β X z => ∑ m ∈ Finset.range (J + 1), ∑ α : DerivativeWord2 m,
    C m α X z * iterSlow m α B m' β X z0

/-- Composition: the outer array `C` applied to the applied field `X ↦ applyArr K B a X z0`
is an applied field of order `J + K`. -/
theorem applyArr_comp (J K : ℕ) (C B : CArr) (a : Vec 2 → ℝ) (z0 : Vec 2)
    (ha : ContDiff ℝ ((K + J : ℕ) : WithTop ℕ∞) a) (hB : ArrSlowSmooth J B) (hs : ArrSupp K B) :
    applyArr J C (fun X => applyArr K B a X z0) =
      applyArr (J + K) (compArr J C B z0) a := by
  funext X z
  show (∑ m ∈ Finset.range (J + 1), ∑ α : DerivativeWord2 m,
    C m α X z * orderedDerivative α (fun X => applyArr K B a X z0) X) = _
  have e1 : ∀ m ∈ Finset.range (J + 1), ∀ α : DerivativeWord2 m,
      orderedDerivative α (fun X => applyArr K B a X z0) X =
        applyArr (J + K) (iterSlow m α B) a X z0 := by
    intro m hm α
    have hm' : m ≤ J := by simpa [Nat.lt_succ_iff] using hm
    rw [congrFun (orderedDerivative_applyArr α K B a z0
      (ha.of_le (by exact_mod_cast (by omega : K + m ≤ K + J))) (hB.mono hm') hs) X]
    exact congrFun (congrFun (applyArr_eq_of_supp (K := K + m) (K' := J + K) (by omega)
      (arrSupp_iterSlow α hs) a).symm X) z0
  rw [Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun α _ => by rw [e1 m hm α]]
  unfold applyArr compArr
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ m ∈ Finset.range (J + 1), ∑ m' ∈ Finset.range (J + K + 1),
          ∑ β : DerivativeWord2 m', ∑ α : DerivativeWord2 m,
            C m α X z * (iterSlow m α B m' β X z0 * orderedDerivative β a X) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m' _ => Finset.sum_comm
    _ = ∑ m' ∈ Finset.range (J + K + 1), ∑ m ∈ Finset.range (J + 1),
          ∑ β : DerivativeWord2 m', ∑ α : DerivativeWord2 m,
            C m α X z * (iterSlow m α B m' β X z0 * orderedDerivative β a X) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun m' _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun m _ =>
          Finset.sum_congr rfl fun α _ => ?_
        rw [mul_assoc]

/-! Joint smoothness and supports of coefficient arrays.

`ArrSmooth r A`: every coefficient is `C^r` in `(X,z)` jointly. This is the regularity class
closed under `slowArr`, `fastArr` (each costs one order), products with jointly smooth functions
and sums. Supports are submodules, so finite and list sums are free. -/

/-- The fast derivative of each coefficient. -/
def fastArr (j : Fin 2) (A : CArr) : CArr :=
  fun m α X z => fastPartial j (A m α) X z

/-- Jointly `C^r` arrays, as a submodule. -/
def arrSmoothSub (r : ℕ) : Submodule ℝ CArr where
  carrier := {A | ∀ m α, ContDiff ℝ (r : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => A m α p.1 p.2)}
  add_mem' := fun ha hb m α => (ha m α).add (hb m α)
  zero_mem' := fun _ _ => contDiff_const
  smul_mem' := fun c _ hA m α => (hA m α).const_smul c

/-- Every coefficient is `C^r` in `(X,z)` jointly. -/
def ArrSmooth (r : ℕ) (A : CArr) : Prop := A ∈ arrSmoothSub r

theorem arrSmooth_def {r : ℕ} {A : CArr} :
    ArrSmooth r A ↔ ∀ m α, ContDiff ℝ (r : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => A m α p.1 p.2) :=
  Iff.rfl

theorem ArrSmooth.mono {r r' : ℕ} (h : r' ≤ r) {A : CArr} (hA : ArrSmooth r A) :
    ArrSmooth r' A :=
  fun m α => (hA m α).of_le (by exact_mod_cast h)

theorem ArrSmooth.zero (r : ℕ) : ArrSmooth r 0 := (arrSmoothSub r).zero_mem

theorem ArrSmooth.add {r : ℕ} {A B : CArr} (hA : ArrSmooth r A) (hB : ArrSmooth r B) :
    ArrSmooth r (A + B) := (arrSmoothSub r).add_mem hA hB

theorem ArrSmooth.smul {r : ℕ} (c : ℝ) {A : CArr} (hA : ArrSmooth r A) : ArrSmooth r (c • A) :=
  (arrSmoothSub r).smul_mem c hA

theorem ArrSmooth.sum {r : ℕ} {ι : Type*} (s : Finset ι) {A : ι → CArr}
    (hA : ∀ i ∈ s, ArrSmooth r (A i)) : ArrSmooth r (∑ i ∈ s, A i) :=
  (arrSmoothSub r).sum_mem hA

theorem ArrSmooth.list_sum {r : ℕ} {l : List CArr} (hA : ∀ A ∈ l, ArrSmooth r A) :
    ArrSmooth r l.sum :=
  (arrSmoothSub r).list_sum_mem hA

/-- Supports, as a submodule. -/
def arrSuppSub (K : ℕ) : Submodule ℝ CArr where
  carrier := {A | ArrSupp K A}
  add_mem' := fun ha hb m hm α => by simp [ha m hm α, hb m hm α]
  zero_mem' := fun m _ α => rfl
  smul_mem' := fun c _ hA m hm α => by simp [hA m hm α]

theorem ArrSupp.zero (K : ℕ) : ArrSupp K 0 := (arrSuppSub K).zero_mem

theorem ArrSupp.add {K : ℕ} {A B : CArr} (hA : ArrSupp K A) (hB : ArrSupp K B) :
    ArrSupp K (A + B) := (arrSuppSub K).add_mem hA hB

theorem ArrSupp.smul {K : ℕ} (c : ℝ) {A : CArr} (hA : ArrSupp K A) : ArrSupp K (c • A) :=
  (arrSuppSub K).smul_mem c hA

theorem ArrSupp.sum {K : ℕ} {ι : Type*} (s : Finset ι) {A : ι → CArr}
    (hA : ∀ i ∈ s, ArrSupp K (A i)) : ArrSupp K (∑ i ∈ s, A i) :=
  (arrSuppSub K).sum_mem hA

theorem ArrSupp.list_sum {K : ℕ} {l : List CArr} (hA : ∀ A ∈ l, ArrSupp K A) :
    ArrSupp K l.sum :=
  (arrSuppSub K).list_sum_mem hA

theorem ArrSupp.mono {K K' : ℕ} (h : K ≤ K') {A : CArr} (hA : ArrSupp K A) : ArrSupp K' A :=
  fun m hm α => hA m (by omega) α

theorem arrSupp_fastArr {K : ℕ} {A : CArr} (j : Fin 2) (hA : ArrSupp K A) :
    ArrSupp K (fastArr j A) := by
  intro m hm α
  funext X z
  simp [fastArr, hA m hm α, fastPartial]

theorem arrSupp_mulArr {K : ℕ} {A : CArr} (g : Vec 2 → Vec 2 → ℝ) (hA : ArrSupp K A) :
    ArrSupp K (mulArr g A) := by
  intro m hm α
  funext X z
  simp [mulArr, hA m hm α]

theorem arrSupp_meanArr {K : ℕ} {A : CArr} (hA : ArrSupp K A) : ArrSupp K (meanArr A) := by
  intro m hm α
  funext X z
  simp [meanArr, hA m hm α, fieldCellMean]

theorem arrSupp_compArr {K : ℕ} (J : ℕ) (C : CArr) {B : CArr} (z0 : Vec 2) (hB : ArrSupp K B) :
    ArrSupp (J + K) (compArr J C B z0) := by
  intro m' hm' β
  funext X z
  unfold compArr
  refine Finset.sum_eq_zero fun m hm => Finset.sum_eq_zero fun α _ => ?_
  have hm2 : m ≤ J := by simpa [Nat.lt_succ_iff] using hm
  have := arrSupp_iterSlow α hB m' (by omega) β
  simp [this]

/-! ### Calculus on jointly smooth arrays -/

theorem fastPartial_eq_fderiv {F : Vec 2 × Vec 2 → ℝ} (hF : Differentiable ℝ F) (j : Fin 2)
    (X z : Vec 2) :
    fastPartial j (fun X z => F (X, z)) X z = fderiv ℝ F (X, z) (0, basisVec j) := by
  unfold fastPartial
  have h1 : HasFDerivAt (fun z' : Vec 2 => (X, z'))
      ((0 : Vec 2 →L[ℝ] Vec 2).prod (ContinuousLinearMap.id ℝ (Vec 2))) z :=
    (hasFDerivAt_const X z).prodMk (hasFDerivAt_id z)
  have h2 := (hF (X, z)).hasFDerivAt.comp z h1
  have h3 : fderiv ℝ (fun z' => F (X, z')) z = _ := h2.fderiv
  show fderiv ℝ (fun z' => F (X, z')) z (basisVec j) = _
  rw [h3]
  simp

theorem slowPartial_eq_fderiv {F : Vec 2 × Vec 2 → ℝ} (hF : Differentiable ℝ F) (j : Fin 2)
    (X z : Vec 2) :
    slowPartial j (fun X z => F (X, z)) X z = fderiv ℝ F (X, z) (basisVec j, 0) := by
  unfold slowPartial
  have h1 : HasFDerivAt (fun X' : Vec 2 => (X', z))
      ((ContinuousLinearMap.id ℝ (Vec 2)).prod (0 : Vec 2 →L[ℝ] Vec 2)) X :=
    (hasFDerivAt_id X).prodMk (hasFDerivAt_const z X)
  have h2 := (hF (X, z)).hasFDerivAt.comp X h1
  have h3 : fderiv ℝ (fun X' => F (X', z)) X = _ := h2.fderiv
  show fderiv ℝ (fun X' => F (X', z)) X (basisVec j) = _
  rw [h3]
  simp

theorem contDiff_fderiv_apply {r : ℕ} {F : Vec 2 × Vec 2 → ℝ}
    (hF : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) F) (e : Vec 2 × Vec 2) :
    ContDiff ℝ (r : WithTop ℕ∞) (fun p => fderiv ℝ F p e) := by
  have h := hF.fderiv_right (m := (r : WithTop ℕ∞)) (by push_cast; exact le_rfl)
  exact h.clm_apply contDiff_const

theorem arrSmooth_fastArr {r : ℕ} {A : CArr} (j : Fin 2) (hA : ArrSmooth (r + 1) A) :
    ArrSmooth r (fastArr j A) := by
  intro m α
  have hF := hA m α
  have hd : Differentiable ℝ (fun p : Vec 2 × Vec 2 => A m α p.1 p.2) :=
    hF.differentiable (by simp)
  have : (fun p : Vec 2 × Vec 2 => fastArr j A m α p.1 p.2) =
      fun p => fderiv ℝ (fun p : Vec 2 × Vec 2 => A m α p.1 p.2) p (0, basisVec j) := by
    funext p
    exact fastPartial_eq_fderiv (F := fun p : Vec 2 × Vec 2 => A m α p.1 p.2) hd j p.1 p.2
  rw [this]
  exact contDiff_fderiv_apply hF _

theorem arrSmooth_slowArr {r : ℕ} {A : CArr} (j : Fin 2) (hA : ArrSmooth (r + 1) A) :
    ArrSmooth r (slowArr j A) := by
  intro m β
  have hF := hA m β
  have hd : Differentiable ℝ (fun p : Vec 2 × Vec 2 => A m β p.1 p.2) :=
    hF.differentiable (by simp)
  have h1 : ContDiff ℝ (r : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => slowPartial j (A m β) p.1 p.2) := by
    have : (fun p : Vec 2 × Vec 2 => slowPartial j (A m β) p.1 p.2) =
        fun p => fderiv ℝ (fun p : Vec 2 × Vec 2 => A m β p.1 p.2) p (basisVec j, 0) := by
      funext p
      exact slowPartial_eq_fderiv (F := fun p : Vec 2 × Vec 2 => A m β p.1 p.2) hd j p.1 p.2
    rw [this]
    exact contDiff_fderiv_apply hF _
  cases m with
  | zero => simpa [slowArr, slowExtra] using h1
  | succ m =>
    simp only [slowArr, slowExtra]
    split_ifs
    · exact h1.add ((hA.mono (Nat.le_succ r)) m _)
    · simpa using h1

theorem arrSmooth_mulArr {r : ℕ} {A : CArr} {g : Vec 2 → Vec 2 → ℝ}
    (hg : ContDiff ℝ (r : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => g p.1 p.2))
    (hA : ArrSmooth r A) : ArrSmooth r (mulArr g A) :=
  fun m α => hg.mul (hA m α)

theorem ArrSmooth.slow {r : ℕ} {A : CArr} (hA : ArrSmooth r A) : ArrSlowSmooth r A :=
  fun m α _ => (hA m α).comp (contDiff_id.prodMk contDiff_const)

theorem ArrSmooth.diff_z {A : CArr} (hA : ArrSmooth 1 A) (m : ℕ) (α : DerivativeWord2 m)
    (X : Vec 2) : Differentiable ℝ (fun z => A m α X z) :=
  ((hA m α).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)

theorem ArrSmooth.continuous {A : CArr} (hA : ArrSmooth 0 A) (m : ℕ) (α : DerivativeWord2 m) :
    Continuous (fun p : Vec 2 × Vec 2 => A m α p.1 p.2) :=
  (hA m α).continuous

/-! ### Linearity of `slowArr` and `fastArr` -/

theorem slowPartial_sum_mul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → Vec 2 → Vec 2 → ℝ)
    (j : Fin 2) (hf : ∀ i ∈ s, ∀ z, Differentiable ℝ (fun X => f i X z)) (X z : Vec 2) :
    slowPartial j (fun X z => ∑ i ∈ s, c i * f i X z) X z =
      ∑ i ∈ s, c i * slowPartial j (f i) X z := by
  unfold slowPartial
  have h := HasFDerivAt.fun_sum (u := s) (fun i hi => ((hf i hi z) X).hasFDerivAt.const_mul (c i))
  rw [h.fderiv]
  simp

theorem fastPartial_sum_mul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → Vec 2 → Vec 2 → ℝ)
    (j : Fin 2) (hf : ∀ i ∈ s, ∀ X, Differentiable ℝ (fun z => f i X z)) (X z : Vec 2) :
    fastPartial j (fun X z => ∑ i ∈ s, c i * f i X z) X z =
      ∑ i ∈ s, c i * fastPartial j (f i) X z := by
  unfold fastPartial
  have h := HasFDerivAt.fun_sum (u := s) (fun i hi => ((hf i hi X) z).hasFDerivAt.const_mul (c i))
  rw [h.fderiv]
  simp

theorem slowArr_sum_smul {ι : Type*} (j : Fin 2) (s : Finset ι) (c : ι → ℝ) (P : ι → CArr)
    (hP : ∀ i ∈ s, ArrSlowSmooth 1 (P i)) :
    slowArr j (∑ i ∈ s, c i • P i) = ∑ i ∈ s, c i • slowArr j (P i) := by
  funext m β X z
  have h1 : slowPartial j ((∑ i ∈ s, c i • P i) m β) X z =
      ∑ i ∈ s, c i * slowPartial j (P i m β) X z := by
    have e : (∑ i ∈ s, c i • P i) m β = fun X z => ∑ i ∈ s, c i * P i m β X z := by
      funext X z; simp [Finset.sum_apply]
    rw [e]
    exact slowPartial_sum_mul s c (fun i => P i m β) j
      (fun i hi z => (hP i hi m β z).differentiable (by simp)) X z
  have h2 : slowExtra j (∑ i ∈ s, c i • P i) m β X z =
      ∑ i ∈ s, c i * slowExtra j (P i) m β X z := by
    cases m with
    | zero => simp [slowExtra]
    | succ m =>
      simp only [slowExtra, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
  have hL : slowArr j (∑ i ∈ s, c i • P i) m β X z =
      slowPartial j ((∑ i ∈ s, c i • P i) m β) X z +
        slowExtra j (∑ i ∈ s, c i • P i) m β X z := rfl
  rw [hL, h1, h2, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, slowArr, Finset.sum_apply]
  simp only [mul_add, Finset.sum_add_distrib]

theorem fastArr_sum_smul {ι : Type*} (j : Fin 2) (s : Finset ι) (c : ι → ℝ) (P : ι → CArr)
    (hP : ∀ i ∈ s, ArrSmooth 1 (P i)) :
    fastArr j (∑ i ∈ s, c i • P i) = ∑ i ∈ s, c i • fastArr j (P i) := by
  funext m β X z
  have e : (∑ i ∈ s, c i • P i) m β = fun X z => ∑ i ∈ s, c i * P i m β X z := by
    funext X z; simp [Finset.sum_apply]
  unfold fastArr
  rw [e]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact fastPartial_sum_mul s c (fun i => P i m β) j (fun i hi X => (hP i hi).diff_z m β X) X z

theorem fastArr_zero (j : Fin 2) : fastArr j 0 = 0 := by
  funext m β X z
  simp [fastArr, fastPartial]

end AVRegularity.Providers.GenSem
end

section
open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory Metric
namespace AVRegularity.Providers.GenSem

/-! The cell mean of a jointly `C^r` array is `C^r` in the slow variable.

Differentiation under the integral sign over the unit cube (a bounded set), by induction on
the order. -/

/-- The closed unit cube, a compact superset of `unitCube`. -/
def closedCube : Set (Vec 2) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem isCompact_closedCube : IsCompact closedCube :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem unitCube_subset_closedCube : AVenhance.unitCube ⊆ closedCube :=
  Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self

theorem measurableSet_unitCube : MeasurableSet AVenhance.unitCube :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem volume_unitCube_lt_top : volume AVenhance.unitCube < ⊤ :=
  lt_of_le_of_lt (measure_mono unitCube_subset_closedCube) isCompact_closedCube.measure_lt_top

instance isFiniteMeasure_restrict_unitCube : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact volume_unitCube_lt_top⟩

theorem integrableOn_unitCube_of_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec 2 → E} (hf : Continuous f) : IntegrableOn f AVenhance.unitCube :=
  (hf.continuousOn.integrableOn_compact isCompact_closedCube).mono_set unitCube_subset_closedCube

theorem exists_bound_cube {E : Type*} [NormedAddCommGroup E] {F : Vec 2 × Vec 2 → E}
    (hF : Continuous F) (X₀ : Vec 2) :
    ∃ M : ℝ, ∀ X ∈ closedBall X₀ 1, ∀ z ∈ AVenhance.unitCube, ‖F (X, z)‖ ≤ M := by
  obtain ⟨M, hM⟩ := ((isCompact_closedBall X₀ 1).prod isCompact_closedCube).bddAbove_image
    hF.norm.continuousOn
  exact ⟨M, fun X hX z hz => hM (Set.mem_image_of_mem _
    (Set.mk_mem_prod hX (unitCube_subset_closedCube hz)))⟩

theorem continuous_cellIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Vec 2 × Vec 2 → E} (hF : Continuous F) :
    Continuous (fun X => ∫ z in AVenhance.unitCube, F (X, z)) := by
  rw [continuous_iff_continuousAt]
  intro X₀
  obtain ⟨M, hM⟩ := exists_bound_cube hF X₀
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun X => (hF.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards [closedBall_mem_nhds X₀ one_pos] with X hX
    rw [ae_restrict_iff' measurableSet_unitCube]
    exact Filter.Eventually.of_forall fun z hz => hM X hX z hz
  · exact integrable_const M
  · exact Filter.Eventually.of_forall fun z => (hF.comp (by fun_prop)).continuousAt

theorem hasFDerivAt_cellIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {F : Vec 2 × Vec 2 → E} (hF : ContDiff ℝ 1 F) (X₀ : Vec 2) :
    HasFDerivAt (fun X => ∫ z in AVenhance.unitCube, F (X, z))
      (∫ z in AVenhance.unitCube,
        (fderiv ℝ F (X₀, z)).comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2))) X₀ := by
  have hG : Continuous fun p : Vec 2 × Vec 2 =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)) :=
    (hF.continuous_fderiv one_ne_zero).clm_comp continuous_const
  obtain ⟨M, hM⟩ := exists_bound_cube hG X₀
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => M)
    (F' := fun X z => (fderiv ℝ F (X, z)).comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)))
    (closedBall_mem_nhds X₀ one_pos) ?_ ?_ ?_ ?_ (integrable_const M) ?_
  · exact Filter.Eventually.of_forall fun X => (hF.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact (integrableOn_unitCube_of_continuous (hF.continuous.comp (by fun_prop)))
  · exact (hG.comp (by fun_prop)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_unitCube]
    exact Filter.Eventually.of_forall fun z hz X hX => hM X hX z hz
  · refine Filter.Eventually.of_forall fun z X _ => ?_
    exact ((hF.differentiable one_ne_zero (X, z)).hasFDerivAt.comp X
      ((hasFDerivAt_id X).prodMk (hasFDerivAt_const z X)))

universe u in
theorem contDiff_cellIntegral : ∀ (r : ℕ) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {F : Vec 2 × Vec 2 → E}, ContDiff ℝ (r : WithTop ℕ∞) F →
    ContDiff ℝ (r : WithTop ℕ∞) (fun X => ∫ z in AVenhance.unitCube, F (X, z)) := by
  intro r
  induction r with
  | zero =>
    intro E _ _ _ F hF
    exact contDiff_zero.mpr (continuous_cellIntegral (contDiff_zero.mp hF))
  | succ r ih =>
    intro E _ _ _ F hF
    have h1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le r))
    have hd : ∀ X, HasFDerivAt (fun X => ∫ z in AVenhance.unitCube, F (X, z)) _ X :=
      hasFDerivAt_cellIntegral h1
    have hG : ContDiff ℝ (r : WithTop ℕ∞) fun p : Vec 2 × Vec 2 =>
        (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)) := by
      have := hF.fderiv_right (m := (r : WithTop ℕ∞)) (by push_cast; exact le_rfl)
      exact this.clm_comp contDiff_const
    have hfd : fderiv ℝ (fun X => ∫ z in AVenhance.unitCube, F (X, z)) =
        fun X => ∫ z in AVenhance.unitCube,
          (fderiv ℝ F (X, z)).comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)) :=
      funext fun X => (hd X).fderiv
    rw [show (((r + 1 : ℕ)) : WithTop ℕ∞) = (r : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_fderiv]
    refine ⟨fun X => (hd X).differentiableAt, by simp, ?_⟩
    rw [hfd]
    exact ih hG

/-- The cell mean of a jointly `C^r` array is `C^r` in the slow variable. -/
theorem arrSlowSmooth_meanArr {r : ℕ} {A : CArr} (hA : ArrSmooth r A) :
    ArrSlowSmooth r (meanArr A) := by
  intro m α z
  exact contDiff_cellIntegral r (hA m α)

theorem arrSmooth_integrableOn {A : CArr} (hA : ArrSmooth 0 A) (m : ℕ) (α : DerivativeWord2 m)
    (X : Vec 2) : IntegrableOn (fun z => A m α X z) AVenhance.unitCube :=
  integrableOn_unitCube_of_continuous
    ((hA.continuous m α).comp (continuous_const.prodMk continuous_id))

end AVRegularity.Providers.GenSem
end
