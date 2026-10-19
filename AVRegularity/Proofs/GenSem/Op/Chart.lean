-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.CoeffArr.Mean
public import AVRegularity.Proofs.GenSem.Jet.JetRepG

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **Slow smoothness of the composed array `compArr`** (its support is `arrSupp_compArr`, in
`CoeffArr.Mean`). -/

theorem arrSlowSmooth_compArr {r : ℕ} (J : ℕ) {C B : CArr} (hC : ArrSlowSmooth r C)
    (hB : ArrSlowSmooth (r + J) B) (z0 : Vec 2) : ArrSlowSmooth r (compArr J C B z0) := by
  intro m' β z
  unfold compArr
  refine ContDiff.sum fun m hm => ContDiff.sum fun α _ => ?_
  have hmJ : m ≤ J := by simpa [Nat.lt_succ_iff] using hm
  exact (hC m α z).mul (arrSlowSmooth_iterSlow (r := r) α (hB.mono (by omega)) m' β z0)

/-- The identity array: `applyArr 0 unitArr f = f`. -/
def unitArr : CArr
  | 0, _, _, _ => 1
  | _, _, _, _ => 0

theorem unitArr_supp : ArrSupp 0 unitArr := by
  intro m hm α
  match m, hm with
  | m + 1, _ => rfl

theorem applyArr_unitArr (f : Vec 2 → ℝ) (x z : Vec 2) : applyArr 0 unitArr f x z = f x := by
  have e : ∀ α : DerivativeWord2 0, orderedDerivative α f x = f x := fun α => by
    rw [Subsingleton.elim α Fin.elim0, orderedDerivative_zero_word]
  simp [applyArr, unitArr, e]

/-! **Composition of array operators (operator forms).** The label operators
`L a y = applyArr K A a y 0` (scalar) and `M a y c = applyArr K (B c) a y 0` (flux, components)
compose to array operators, and the entries of the composed array have represented jets
(`arrJetG_compArr`). -/

/-- **Scalar `C ∘ L`**: the outer array `C` (order `J`) applied to the operator `L` of order `K`. -/
theorem opComp_eq (J K : ℕ) (C B : CArr) (a : Vec 2 → ℝ)
    (ha : ContDiff ℝ ((K + J : ℕ) : WithTop ℕ∞) a) (hB : ArrSlowSmooth J B) (hs : ArrSupp K B)
    (y : Vec 2) :
    applyArr J C (fun X => applyArr K B a X 0) y 0 = applyArr (J + K) (compArr J C B 0) a y 0 :=
  congrFun (congrFun (applyArr_comp J K C B a 0 ha hB hs) y) 0

/-- **`C ∘ M`**, `M` flux-valued with component arrays `B c`, `C` scalar: componentwise. -/
theorem opComp_flux_left (J K : ℕ) (C : CArr) (B : Fin 2 → CArr) (a : Vec 2 → ℝ)
    (ha : ContDiff ℝ ((K + J : ℕ) : WithTop ℕ∞) a) (hB : ∀ c, ArrSlowSmooth J (B c))
    (hs : ∀ c, ArrSupp K (B c)) (y : Vec 2) (c : Fin 2) :
    applyArr J C (fun X => applyArr K (B c) a X 0) y 0 =
      applyArr (J + K) (compArr J C (B c) 0) a y 0 :=
  opComp_eq J K C (B c) a ha (hB c) (hs c) y

/-- **`M ∘ C`**, `M` flux-valued with component arrays `B c` of order `K`, `C` scalar of order `J`:
the component `c` of `M (C a)`. -/
theorem opComp_flux_right (K J : ℕ) (B : Fin 2 → CArr) (C : CArr) (a : Vec 2 → ℝ)
    (ha : ContDiff ℝ ((J + K : ℕ) : WithTop ℕ∞) a) (hC : ArrSlowSmooth K C) (hs : ArrSupp J C)
    (y : Vec 2) (c : Fin 2) :
    applyArr K (B c) (fun X => applyArr J C a X 0) y 0 =
      applyArr (K + J) (compArr K (B c) C 0) a y 0 :=
  opComp_eq K J (B c) C a ha hC hs y

/-! **Faà di Bruno arrays.** For a label map `Φ`, `fdbArr Φ α` is the array (entries
functions of the label `w`, `z` a dummy) with
`∂^α (f ∘ Φ) (w) = ∑_{m ≤ |α|} ∑_γ fdbArr Φ α m γ w z * ∂^γ f (Φ w)`.
It is built by the recursion `fdbStep` (a slow derivative of the coefficients plus the chain-rule
term `A (m-1) (init β) * ∂_i Φ_{β last}`), exactly like `iterSlow`. -/

/-- `∑_{m ≤ K} ∑_γ A m γ w z * ∂^γ f (Φ w)`: the array `A` applied to `f` at the point `Φ w`. -/
def applyFdb (K : ℕ) (A : CArr) (f : Vec 2 → ℝ) (Φ : Vec 2 → Vec 2) (z : Vec 2) : Vec 2 → ℝ :=
  fun w => ∑ m ∈ Finset.range (K + 1), ∑ γ : DerivativeWord2 m,
    A m γ w z * orderedDerivative γ f (Φ w)

/-- The chain-rule extra coefficient. -/
def fdbExtra (Φ : Vec 2 → Vec 2) (i : Fin 2) (A : CArr) : CArr
  | 0, _, _, _ => 0
  | m + 1, β, w, z => A m (Fin.init β) w z * fderiv ℝ Φ w (basisVec i) (β (Fin.last m))

/-- One differentiation of `applyFdb` in the direction `i`. -/
def fdbStep (Φ : Vec 2 → Vec 2) (i : Fin 2) (A : CArr) : CArr :=
  fun m β w z => slowPartial i (A m β) w z + fdbExtra Φ i A m β w z

/-- Iterated steps along a word (letters `α 0, α 1, …` in this order). -/
def fdbIter (Φ : Vec 2 → Vec 2) : (n : ℕ) → DerivativeWord2 n → CArr → CArr
  | 0, _, B => B
  | n + 1, α, B => fdbIter Φ n (fun i => α i.succ) (fdbStep Φ (α 0) B)

/-- The Faà di Bruno array of the word `α`. -/
def fdbArr (Φ : Vec 2 → Vec 2) {n : ℕ} (α : DerivativeWord2 n) : CArr :=
  fdbIter Φ n α unitArr

theorem differentiable_orderedDerivative_top {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {m : ℕ}
    (γ : DerivativeWord2 m) : Differentiable ℝ (orderedDerivative γ f) :=
  orderedDerivative_differentiable γ
    ((fun n : ℕ => (hf.of_le (by exact_mod_cast le_top) : ContDiff ℝ (n : WithTop ℕ∞) f)) _)

/-- Reindexing of the chain-rule extra coefficients through `Fin.snoc`. -/
theorem sum_fdbExtra (Φ : Vec 2 → Vec 2) (i : Fin 2) (A : CArr) (m : ℕ) (w z : Vec 2)
    (G : DerivativeWord2 (m + 1) → ℝ) :
    ∑ β : DerivativeWord2 (m + 1), fdbExtra Φ i A (m + 1) β w z * G β =
      ∑ α : DerivativeWord2 m, ∑ b : Fin 2,
        A m α w z * fderiv ℝ Φ w (basisVec i) b * G (Fin.snoc α b) := by
  classical
  rw [← (Fin.snocEquiv (fun _ : Fin (m + 1) => Fin 2)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun b _ => ?_
  have e : (Fin.snocEquiv (fun _ : Fin (m + 1) => Fin 2)) (b, α) = Fin.snoc α b := rfl
  simp [e, fdbExtra]

/-- **One differentiation of `applyFdb`.** -/
theorem fderiv_applyFdb (K : ℕ) (A : CArr) {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {Φ : Vec 2 → Vec 2} (hΦ : Differentiable ℝ Φ) (z : Vec 2) (i : Fin 2)
    (hA : ∀ m α, Differentiable ℝ (fun w => A m α w z)) (hs : ArrSupp K A) (w : Vec 2) :
    fderiv ℝ (applyFdb K A f Φ z) w (basisVec i) = applyFdb (K + 1) (fdbStep Φ i A) f Φ z w := by
  have key : ∀ m ∈ Finset.range (K + 1), ∀ (γ : DerivativeWord2 m),
      HasFDerivAt (fun w' => A m γ w' z * orderedDerivative γ f (Φ w'))
        (A m γ w z • ((fderiv ℝ (orderedDerivative γ f) (Φ w)).comp (fderiv ℝ Φ w)) +
          orderedDerivative γ f (Φ w) • fderiv ℝ (fun w' => A m γ w' z) w) w := fun m _ γ =>
    ((hA m γ) w).hasFDerivAt.mul
      (((differentiable_orderedDerivative_top hf γ) (Φ w)).hasFDerivAt.comp w
        (hΦ w).hasFDerivAt)
  have h := HasFDerivAt.fun_sum (u := Finset.range (K + 1))
    (fun m hm => HasFDerivAt.fun_sum (u := (Finset.univ : Finset (DerivativeWord2 m)))
      (fun γ _ => key m hm γ))
  unfold applyFdb
  rw [h.fderiv]
  simp only [sum_apply, add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.coe_comp,
    Function.comp_apply, fdbStep, add_mul, Finset.sum_add_distrib]
  have hE : ∑ x ∈ Finset.range (K + 1 + 1), ∑ β : DerivativeWord2 x,
      fdbExtra Φ i A x β w z * orderedDerivative β f (Φ w) =
      ∑ x ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 x,
        A x α w z * (fderiv ℝ (orderedDerivative α f) (Φ w)) (fderiv ℝ Φ w (basisVec i)) := by
    rw [Finset.sum_range_succ']
    have h0 : ∀ β : DerivativeWord2 0, fdbExtra Φ i A 0 β w z = 0 := fun _ => rfl
    simp only [h0, Finset.sum_const_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [sum_fdbExtra Φ i A m w z (fun β => orderedDerivative β f (Φ w))]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hv : fderiv ℝ Φ w (basisVec i) =
        ∑ b : Fin 2, (fderiv ℝ Φ w (basisVec i) b) • basisVec b := by
      funext a; simp [Finset.sum_apply, basisVec, Pi.single_apply]
    conv_rhs => rw [hv]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, smul_eq_mul, orderedDerivative_snoc]
    ring
  have hP : ∑ x ∈ Finset.range (K + 1 + 1), ∑ β : DerivativeWord2 x,
      slowPartial i (A x β) w z * orderedDerivative β f (Φ w) =
      ∑ x ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 x,
        orderedDerivative α f (Φ w) * (fderiv ℝ (fun w' => A x α w' z) w) (basisVec i) := by
    rw [Finset.sum_range_succ]
    have : ∀ β : DerivativeWord2 (K + 1),
        slowPartial i (A (K + 1) β) w z * orderedDerivative β f (Φ w) = 0 := fun β => by
      rw [hs (K + 1) (by omega) β]; simp [slowPartial]
    simp only [this, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun α _ => ?_
    rw [mul_comm]; rfl
  rw [hE, hP, add_comm]

theorem arrSupp_fdbStep {K : ℕ} {A : CArr} (Φ : Vec 2 → Vec 2) (i : Fin 2) (hA : ArrSupp K A) :
    ArrSupp (K + 1) (fdbStep Φ i A) := by
  intro m hm β
  funext w z
  have h0 : slowPartial i (A m β) w z = 0 := by
    rw [hA m (by omega) β]; simp [slowPartial]
  cases m with
  | zero => omega
  | succ m =>
    have : A m = 0 := funext fun α => hA m (by omega) α
    simp only [fdbStep, h0, fdbExtra, this, Pi.zero_apply, zero_mul, add_zero]

theorem arrSupp_fdbIter {K : ℕ} (Φ : Vec 2 → Vec 2) : ∀ {n : ℕ} (α : DerivativeWord2 n) {B : CArr},
    ArrSupp K B → ArrSupp (K + n) (fdbIter Φ n α B) := by
  intro n
  induction n generalizing K with
  | zero => intro α B h; simpa [fdbIter] using h
  | succ n ih =>
    intro α B h
    have := ih (K := K + 1) (fun i => α i.succ) (arrSupp_fdbStep Φ (α 0) h)
    rwa [show K + 1 + n = K + (n + 1) by omega] at this

/-- Entries of the Jacobian of a smooth map are smooth of every finite order. -/
theorem contDiff_fderiv_entry {Φ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (r : ℕ)
    (i b : Fin 2) : ContDiff ℝ (r : WithTop ℕ∞) (fun w => fderiv ℝ Φ w (basisVec i) b) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) b).contDiff.comp
    (contDiff_dirDeriv_nat (r := r)
      ((fun n : ℕ => (hΦ.of_le (by exact_mod_cast le_top) : ContDiff ℝ (n : WithTop ℕ∞) Φ)) _) i)

theorem arrSlowSmooth_fdbStep {r : ℕ} {A : CArr} {Φ : Vec 2 → Vec 2}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin 2) (hA : ArrSlowSmooth (r + 1) A) :
    ArrSlowSmooth r (fdbStep Φ i A) := by
  intro m β z
  have h1 : ContDiff ℝ (r : WithTop ℕ∞) (fun X => slowPartial i (A m β) X z) :=
    contDiff_dirDeriv_nat (hA m β z) i
  cases m with
  | zero => simpa [fdbStep, fdbExtra] using h1
  | succ m =>
    simp only [fdbStep, fdbExtra]
    exact h1.add (((hA.mono (Nat.le_succ r)) m _ z).mul (contDiff_fderiv_entry hΦ r i _))

theorem arrSlowSmooth_fdbIter {r : ℕ} {Φ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ∀ {n : ℕ} (α : DerivativeWord2 n) {B : CArr},
      ArrSlowSmooth (r + n) B → ArrSlowSmooth r (fdbIter Φ n α B) := by
  intro n
  induction n with
  | zero => intro α B h; simpa [fdbIter] using h
  | succ n ih =>
    intro α B h
    exact ih (fun i => α i.succ) (arrSlowSmooth_fdbStep hΦ (α 0) (by
      simpa [add_assoc, add_comm 1 n] using h))

/-- **Ordered derivatives of `applyFdb`.** -/
theorem orderedDerivative_applyFdb {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {Φ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (z : Vec 2) :
    ∀ {n : ℕ} (α : DerivativeWord2 n) (K : ℕ) (A : CArr), ArrSlowSmooth n A → ArrSupp K A →
      orderedDerivative α (applyFdb K A f Φ z) = applyFdb (K + n) (fdbIter Φ n α A) f Φ z := by
  intro n
  induction n with
  | zero =>
    intro α K A _ _
    have : α = Fin.elim0 := Subsingleton.elim _ _
    subst this
    rw [orderedDerivative_zero_word]; rfl
  | succ n ih =>
    intro α K A hA hs
    rw [orderedDerivative_succ]
    have h1 : (fun x => fderiv ℝ (applyFdb K A f Φ z) x (basisVec (α 0))) =
        applyFdb (K + 1) (fdbStep Φ (α 0) A) f Φ z := funext fun w =>
      fderiv_applyFdb K A hf (hΦ.differentiable (by simp)) z (α 0)
        (fun m γ => (hA m γ z).differentiable (by norm_cast)) hs w
    rw [h1, ih (fun i => α i.succ) (K + 1) _ (arrSlowSmooth_fdbStep (r := n) hΦ _ hA)
      (arrSupp_fdbStep Φ _ hs)]
    rw [show K + 1 + n = K + (n + 1) by omega]
    rfl

theorem arrSlowSmooth_unitArr (r : ℕ) : ArrSlowSmooth r unitArr := by
  intro m α z
  cases m with
  | zero => exact contDiff_const
  | succ m => exact contDiff_const

theorem arrSupp_fdbArr (Φ : Vec 2 → Vec 2) {n : ℕ} (α : DerivativeWord2 n) :
    ArrSupp n (fdbArr Φ α) := by
  have := arrSupp_fdbIter Φ α unitArr_supp
  rwa [zero_add] at this

theorem arrSlowSmooth_fdbArr {Φ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (r : ℕ) {n : ℕ}
    (α : DerivativeWord2 n) : ArrSlowSmooth r (fdbArr Φ α) :=
  arrSlowSmooth_fdbIter hΦ α (arrSlowSmooth_unitArr _)

/-- **Faà di Bruno**: `∂^α (f ∘ Φ) (w) = ∑_{m ≤ |α|} ∑_γ fdbArr Φ α m γ w * ∂^γ f (Φ w)`
for smooth `f` and smooth `Φ`. -/
theorem orderedDerivative_comp_fdb {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {Φ : Vec 2 → Vec 2} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {n : ℕ} (α : DerivativeWord2 n)
    (w : Vec 2) :
    orderedDerivative α (fun y => f (Φ y)) w =
      ∑ m ∈ Finset.range (n + 1), ∑ γ : DerivativeWord2 m,
        fdbArr Φ α m γ w 0 * orderedDerivative γ f (Φ w) := by
  have e : (fun y => f (Φ y)) = applyFdb 0 unitArr f Φ 0 := by
    funext y
    have e0 : ∀ γ : DerivativeWord2 0, orderedDerivative γ f (Φ y) = f (Φ y) := fun γ => by
      rw [Subsingleton.elim γ Fin.elim0, orderedDerivative_zero_word]
    simp [applyFdb, unitArr, e0]
  rw [e, orderedDerivative_applyFdb hf hΦ 0 α 0 unitArr (arrSlowSmooth_unitArr _) unitArr_supp,
    zero_add]
  rfl

/-! **The constant-coefficient second-order operator as a coefficient array.**
`covArr H` has the entry `H i j` at the word `![j, i]` (letter `j` innermost, `i` outermost),
so that `covOperator H f = applyArr 2 (covArr H) f · 0`. -/

/-- The array of `∑ H i j ∂_i ∂_j`: entry `H (α 1) (α 0)` at the words of order `2`. -/
def covArr (H : Matrix (Fin 2) (Fin 2) ℝ) : CArr
  | 2, α, _, _ => H (α 1) (α 0)
  | _, _, _, _ => 0

/-- **`covOperator` as an array operator** (no smoothness needed: both sides are `fderiv`s). -/
theorem covOperator_eq_applyArr (H : Matrix (Fin 2) (Fin 2) ℝ) (f : Vec 2 → ℝ) (x z : Vec 2) :
    covOperator H f x = applyArr 2 (covArr H) f x z := by
  unfold applyArr
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  have h0 : ∀ α : DerivativeWord2 0, covArr H 0 α x z = 0 := fun _ => rfl
  have h1 : ∀ α : DerivativeWord2 1, covArr H 1 α x z = 0 := fun _ => rfl
  simp only [h0, h1, zero_mul, Finset.sum_const_zero, zero_add]
  change _ = ∑ α : Fin 2 → Fin 2, H (α 1) (α 0) * orderedDerivative α f x
  rw [← (finTwoArrowEquiv (Fin 2)).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  unfold covOperator
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e : ((finTwoArrowEquiv (Fin 2)).symm (j, i) : Fin 2 → Fin 2) = Fin.snoc (![j] : Fin 1 → Fin 2) i := by
    funext k; fin_cases k <;> simp [finTwoArrowEquiv, Fin.snoc]
  rw [e, orderedDerivative_snoc]
  have e1 : orderedDerivative (![j] : DerivativeWord2 1) f = fun y => fderiv ℝ f y (basisVec j) := by
    have : (![j] : Fin 1 → Fin 2) = Fin.snoc (Fin.elim0 : Fin 0 → Fin 2) j := by
      funext k; fin_cases k; simp [Fin.snoc]
    rw [this, orderedDerivative_snoc, orderedDerivative_zero_word]
  rw [e1]
  simp [smul_eq_mul]

/-- The array of the `a`-th iterate of `covOperator H`. -/
def covArrPow (H : Matrix (Fin 2) (Fin 2) ℝ) : ℕ → CArr
  | 0 => unitArr
  | a + 1 => compArr 2 (covArr H) (covArrPow H a) 0

theorem covArrPow_supp (H : Matrix (Fin 2) (Fin 2) ℝ) :
    ∀ a, ArrSupp (2 * a) (covArrPow H a)
  | 0 => unitArr_supp
  | a + 1 => by
      have := arrSupp_compArr 2 (covArr H) (0 : Vec 2) (covArrPow_supp H a)
      rwa [show 2 + 2 * a = 2 * (a + 1) by ring] at this

theorem covArr_slowSmooth (H : Matrix (Fin 2) (Fin 2) ℝ) (r : ℕ) : ArrSlowSmooth r (covArr H) := by
  intro m α z
  cases m with
  | zero => exact contDiff_const
  | succ m => match m with
    | 0 => exact contDiff_const
    | 1 => exact contDiff_const
    | m + 2 => exact contDiff_const

theorem covArrPow_slowSmooth (H : Matrix (Fin 2) (Fin 2) ℝ) (r : ℕ) :
    ∀ a, ArrSlowSmooth r (covArrPow H a)
  | 0 => by
      intro m α z
      cases m with
      | zero => exact contDiff_const
      | succ m => exact contDiff_const
  | a + 1 => arrSlowSmooth_compArr 2 (covArr_slowSmooth H r) (covArrPow_slowSmooth H (r + 2) a) 0

/-- **Iterates of `covOperator` as array operators.** -/
theorem covOperator_iterate_eq (H : Matrix (Fin 2) (Fin 2) ℝ) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∀ (a : ℕ) (x z : Vec 2),
      (covOperator H)^[a] f x = applyArr (2 * a) (covArrPow H a) f x z
  | 0, x, z => by simp [applyArr_unitArr, covArrPow]
  | a + 1, x, z => by
      have hf2 : ContDiff ℝ ((2 * a + 2 : ℕ) : WithTop ℕ∞) f :=
        (fun n : ℕ => (hf.of_le (by exact_mod_cast le_top) : ContDiff ℝ (n : WithTop ℕ∞) f)) _
      have ih : (covOperator H)^[a] f = fun X => applyArr (2 * a) (covArrPow H a) f X 0 :=
        funext fun X => covOperator_iterate_eq H hf a X 0
      rw [Function.iterate_succ_apply', ih, covOperator_eq_applyArr H _ x z,
        applyArr_comp 2 (2 * a) (covArr H) (covArrPow H a) f 0
          hf2 (covArrPow_slowSmooth H 2 a) (covArrPow_supp H a)]
      rw [show 2 + 2 * a = 2 * (a + 1) by ring]
      rfl

end AVRegularity.Providers.GenSem
end

section
open Homogenization AVRegularity AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Providers.GenSem

/-! **Represented jets of label coefficient arrays.** A family (indexed by `Λ`) of arrays
`B l : CArr`, read on the slice `z = 0` (label operators do not depend on the fast variable), has
`ArrJetG R r B` when every entry `y ↦ B l m α y 0` has represented jets of order `r` and is `C^r`.
Closed under the slow derivative `slowArr`, its iterates, and the composition array `compArr`. -/

variable {Λ : Type*} {R : (Λ → ℝ) → Prop}

variable (R) in
/-- Represented jets of order `r` (and `C^r` regularity) of all entries of a family of arrays. -/
def ArrJetG (r : ℕ) (B : Λ → CArr) : Prop :=
  ∀ m (α : DerivativeWord2 m),
    JetRepG R r (fun l y => B l m α y 0) ∧ ∀ l, ContDiff ℝ r (fun y => B l m α y 0)

theorem ArrJetG.mono {r r' : ℕ} (h : r' ≤ r) {B : Λ → CArr} (hB : ArrJetG R r B) :
    ArrJetG R r' B :=
  fun m α => ⟨(hB m α).1.mono h, fun l => ((hB m α).2 l).of_le (by exact_mod_cast h)⟩

/-- A function constant in the label with represented value has represented jets. -/
theorem jetRepG_labelConst (hR : RepAlg R) {F : Λ → ℝ} (hF : R F) :
    ∀ r : ℕ, JetRepG R r (fun l (_ : Vec 2) => F l)
  | 0 => hF
  | r + 1 => ⟨hF, fun j => (jetRepG_const hR r 0).congr_germ fun l =>
      Filter.Eventually.of_forall fun y => by simp [dLabelG]⟩

theorem JetRepG.finsetSum (hR : RepAlg R) {r : ℕ} {κ : Type*} (s : Finset κ)
    {F : κ → Λ → Vec 2 → ℝ} (hc : ∀ k ∈ s, ∀ l, ContDiff ℝ r (F k l))
    (h : ∀ k ∈ s, JetRepG R r (F k)) : JetRepG R r (fun l y => ∑ k ∈ s, F k l y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact (jetRepG_const hR r 0).congr_germ fun l => Filter.Eventually.of_forall fun y => by simp
  | insert a s ha ih =>
    exact (JetRepG.add hR (hc a (Finset.mem_insert_self a s))
      (fun l => ContDiff.sum fun k hk => hc k (Finset.mem_insert_of_mem hk) l)
      (h a (Finset.mem_insert_self a s))
      (ih (fun k hk => hc k (Finset.mem_insert_of_mem hk))
        fun k hk => h k (Finset.mem_insert_of_mem hk))).congr_germ fun l =>
        Filter.Eventually.of_forall fun y => by simp only [Finset.sum_insert ha]

theorem arrJetG_slowArr (hR : RepAlg R) {r : ℕ} {B : Λ → CArr} (j : Fin 2)
    (hB : ArrJetG R (r + 1) B) : ArrJetG R r (fun l => slowArr j (B l)) := by
  intro m β
  have hd : JetRepG R r (dLabelG j (fun l y => B l m β y 0)) := (hB m β).1.2 j
  have hcd : ∀ l, ContDiff ℝ r (fun y => fderiv ℝ (fun X' => B l m β X' 0) y (basisVec j)) := fun l =>
    contDiff_dirDeriv_nat ((hB m β).2 l) j
  cases m with
  | zero =>
    refine ⟨hd.congr_germ fun l => Filter.Eventually.of_forall fun y => ?_, fun l => ?_⟩
    · simp [dLabelG, slowArr, slowExtra, slowPartial]
    · simpa [slowArr, slowExtra, dLabelG, slowPartial]
        using hcd l
  | succ m =>
    by_cases hj : β (Fin.last m) = j
    · have hr : JetRepG R r (fun l y => B l m (Fin.init β) y 0) :=
        (hB m (Fin.init β)).1.mono (Nat.le_succ r)
      have hrc : ∀ l, ContDiff ℝ r (fun y => B l m (Fin.init β) y 0) := fun l =>
        ((hB m (Fin.init β)).2 l).of_le (by exact_mod_cast Nat.le_succ r)
      refine ⟨(JetRepG.add hR hcd hrc hd hr).congr_germ fun l =>
        Filter.Eventually.of_forall fun y => ?_, fun l => ?_⟩
      · simp [slowArr, slowExtra, slowPartial, hj]
      · have := (hcd l).add (hrc l)
        simpa [slowArr, slowExtra, slowPartial, hj,
          dLabelG] using this
    · refine ⟨hd.congr_germ fun l => Filter.Eventually.of_forall fun y => ?_, fun l => ?_⟩
      · simp [dLabelG, slowArr, slowExtra, slowPartial, hj]
      · simpa [slowArr, slowExtra, slowPartial, hj] using hcd l

theorem arrJetG_iterSlow (hR : RepAlg R) {r : ℕ} : ∀ {n : ℕ} (α : DerivativeWord2 n)
    {B : Λ → CArr}, ArrJetG R (r + n) B → ArrJetG R r (fun l => iterSlow n α (B l))
  | 0, _, _, h => h
  | n + 1, α, _, h =>
      arrJetG_iterSlow hR (fun i => α i.succ)
        (arrJetG_slowArr hR (α 0) (by simpa [add_assoc, add_comm 1 n] using h))

/-- **Jets of the composition array.** -/
theorem arrJetG_compArr (hR : RepAlg R) {r : ℕ} (J : ℕ) {C B : Λ → CArr}
    (hC : ArrJetG R r C) (hB : ArrJetG R (r + J) B) :
    ArrJetG R r (fun l => compArr J (C l) (B l) 0) := by
  intro m' β
  have hit : ∀ m ∈ Finset.range (J + 1), ∀ α : DerivativeWord2 m,
      ArrJetG R r (fun l => iterSlow m α (B l)) := fun m hm α =>
    arrJetG_iterSlow hR α (hB.mono (by simp at hm; omega))
  have hterm : ∀ m ∈ Finset.range (J + 1), ∀ α : DerivativeWord2 m,
      JetRepG R r (fun l y => C l m α y 0 * iterSlow m α (B l) m' β y 0) := fun m hm α =>
    JetRepG.mul hR ((hC m α).2) ((hit m hm α m' β).2) (hC m α).1 (hit m hm α m' β).1
  have hsm : ∀ m ∈ Finset.range (J + 1), ∀ α : DerivativeWord2 m, ∀ l,
      ContDiff ℝ r (fun y => C l m α y 0 * iterSlow m α (B l) m' β y 0) := fun m hm α l =>
    ((hC m α).2 l).mul ((hit m hm α m' β).2 l)
  refine ⟨?_, fun l => ?_⟩
  · refine (JetRepG.finsetSum hR (r := r) (Finset.range (J + 1))
      (F := fun m l y => ∑ α : DerivativeWord2 m,
        C l m α y 0 * iterSlow m α (B l) m' β y 0)
      (fun m hm l => ContDiff.sum fun α _ => hsm m hm α l) (fun m hm => ?_)).congr_germ
      fun l => Filter.Eventually.of_forall fun y => rfl
    exact JetRepG.finsetSum hR Finset.univ (fun α _ l => hsm m hm α l) (fun α _ => hterm m hm α)
  · exact ContDiff.sum fun m hm => ContDiff.sum fun α _ => hsm m hm α l

theorem arrJetG_unitArr (hR : RepAlg R) (r : ℕ) : ArrJetG R r (fun _ : Λ => unitArr) := by
  intro m α
  cases m with
  | zero => exact ⟨jetRepG_const hR r 1, fun _ => contDiff_const⟩
  | succ m => exact ⟨jetRepG_const hR r 0, fun _ => contDiff_const⟩

end AVRegularity.Providers.GenSem
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **Represented jets of the Faà di Bruno arrays.** If every component of the family of
label maps `Φ l` (smooth, `C^∞`) has represented jets of order `r + n`, every entry of
`fdbArr (Φ l) α`, `|α| = n`, has represented jets of order `r`. -/

section
variable {Λ : Type*} {R : (Λ → ℝ) → Prop}

/-- The first-derivative entries of a family of label maps have represented jets. -/
theorem jetRepG_fderiv_entry {Φ : Λ → Vec 2 → Vec 2} {r : ℕ}
    (hΦ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Φ l)) (hJ : ∀ b, JetRepG R (r + 1) (fun l y => Φ l y b))
    (i b : Fin 2) : JetRepG R r (fun l y => fderiv ℝ (Φ l) y (basisVec i) b) := by
  refine ((hJ b).2 i).congr_germ fun l => Filter.Eventually.of_forall fun y => ?_
  exact fderiv_component (((hΦ l).differentiable (by simp)) y) b i

theorem arrJetG_fdbStep (hR : RepAlg R) {r : ℕ} {A : Λ → CArr} {Φ : Λ → Vec 2 → Vec 2}
    (hΦ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Φ l)) (hJ : ∀ b, JetRepG R (r + 1) (fun l y => Φ l y b))
    (i : Fin 2) (hA : ArrJetG R (r + 1) A) : ArrJetG R r (fun l => fdbStep (Φ l) i (A l)) := by
  intro m β
  have hd : JetRepG R r (dLabelG i (fun l y => A l m β y 0)) := (hA m β).1.2 i
  have hcd : ∀ l, ContDiff ℝ r (fun y => fderiv ℝ (fun X' => A l m β X' 0) y (basisVec i)) :=
    fun l => contDiff_dirDeriv_nat ((hA m β).2 l) i
  cases m with
  | zero =>
    refine ⟨hd.congr_germ fun l => Filter.Eventually.of_forall fun y => ?_, fun l => ?_⟩
    · simp [fdbStep, fdbExtra, slowPartial, dLabelG]
    · simpa [fdbStep, fdbExtra, slowPartial] using hcd l
  | succ m =>
    have hr : JetRepG R r (fun l y => A l m (Fin.init β) y 0) :=
      (hA m (Fin.init β)).1.mono (Nat.le_succ r)
    have hrc : ∀ l, ContDiff ℝ r (fun y => A l m (Fin.init β) y 0) := fun l =>
      ((hA m (Fin.init β)).2 l).of_le (by exact_mod_cast Nat.le_succ r)
    have hm := JetRepG.mul hR hrc (fun l => contDiff_fderiv_entry (hΦ l) r i (β (Fin.last m)))
      hr (jetRepG_fderiv_entry hΦ hJ i (β (Fin.last m)))
    refine ⟨(JetRepG.add hR hcd (fun l => (hrc l).mul
      (contDiff_fderiv_entry (hΦ l) r i (β (Fin.last m)))) hd hm).congr_germ fun l =>
        Filter.Eventually.of_forall fun y => ?_, fun l => ?_⟩
    · simp [fdbStep, fdbExtra, slowPartial]
    · simpa [fdbStep, fdbExtra, slowPartial] using
        (hcd l).add ((hrc l).mul (contDiff_fderiv_entry (hΦ l) r i (β (Fin.last m))))

theorem arrJetG_fdbIter (hR : RepAlg R) {r : ℕ} {Φ : Λ → Vec 2 → Vec 2}
    (hΦ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Φ l)) :
    ∀ {n : ℕ} (α : DerivativeWord2 n) {A : Λ → CArr},
      (∀ b, JetRepG R (r + n) (fun l y => Φ l y b)) → ArrJetG R (r + n) A →
      ArrJetG R r (fun l => fdbIter (Φ l) n α (A l))
  | 0, _, _, _, h => h
  | n + 1, α, _, hJ, h =>
      arrJetG_fdbIter hR hΦ (fun i => α i.succ)
        (fun b => (hJ b).mono (by omega))
        (arrJetG_fdbStep hR hΦ (fun b => by
          simpa [add_assoc, add_comm 1 n] using hJ b) (α 0)
          (by simpa [add_assoc, add_comm 1 n] using h))

/-- **Jets of the Faà di Bruno array.** -/
theorem arrJetG_fdbArr (hR : RepAlg R) {r n : ℕ} {Φ : Λ → Vec 2 → Vec 2}
    (hΦ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Φ l)) (hJ : ∀ b, JetRepG R (r + n) (fun l y => Φ l y b))
    (α : DerivativeWord2 n) : ArrJetG R r (fun l => fdbArr (Φ l) α) :=
  arrJetG_fdbIter hR hΦ α hJ (arrJetG_unitArr hR _)
end

/-! **Represented jets of the arrays of the covariance operator and its iterates.**
If every entry of the matrix family `H l` is represented (`R`), then all entries of `covArr (H l)`
and of `covArrPow (H l) a` have represented jets of every order. -/

section
variable {Λ : Type*} {R : (Λ → ℝ) → Prop}

theorem arrJetG_covArr (hR : RepAlg R) {H : Λ → Matrix (Fin 2) (Fin 2) ℝ}
    (hH : ∀ i j, R (fun l => H l i j)) (r : ℕ) : ArrJetG R r (fun l => covArr (H l)) := by
  intro m α
  match m with
  | 0 => exact ⟨jetRepG_const hR r 0, fun _ => contDiff_const⟩
  | 1 => exact ⟨jetRepG_const hR r 0, fun _ => contDiff_const⟩
  | 2 => exact ⟨jetRepG_labelConst hR (hH (α 1) (α 0)) r, fun _ => contDiff_const⟩
  | m + 3 => exact ⟨jetRepG_const hR r 0, fun _ => contDiff_const⟩

theorem arrJetG_covArrPow (hR : RepAlg R) {H : Λ → Matrix (Fin 2) (Fin 2) ℝ}
    (hH : ∀ i j, R (fun l => H l i j)) (a : ℕ) :
    ∀ r, ArrJetG R r (fun l => covArrPow (H l) a) := by
  induction a with
  | zero => exact fun r => arrJetG_unitArr hR r
  | succ a ih => exact fun r => arrJetG_compArr hR 2 (arrJetG_covArr hR hH r) (ih (r + 2))
end

/-! **Push and pull of array operators by a chart pair.** A flux operator with component
arrays `A k` (`L g y k = applyArr K (A k) g y 0`) is transformed by the chart germ `Ψ`
(`g ↦ g ∘ Ψ`, evaluation at `N p` with `Ψ (N p) = p`, then the matrix `M p`) into the array operator
with `chartArr M N Ψ K A`. `pushFlux Ψ Ψinv` is the case `M p = DΨ(Ψinv p)`, `N = Ψinv`;
`pullFlux Φ Φinv` is `M p = (DΦ p)⁻¹`, `N = Φ`, `Ψ = Φinv`. -/

/-- The coefficient at the output point `p` of component `c`, order `m'`, word `γ`. -/
def chartCoef (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (N Ψ : Vec 2 → Vec 2) (K : ℕ)
    (A : Fin 2 → CArr) (c : Fin 2) (m' : ℕ) (γ : DerivativeWord2 m') (p : Vec 2) : ℝ :=
  ∑ k : Fin 2, M p c k * ∑ m ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 m,
    A k m α (N p) 0 * fdbArr Ψ α m' γ (N p) 0

/-- The array of the transformed operator (component `c`), constant in `z`. -/
def chartArr (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (N Ψ : Vec 2 → Vec 2) (K : ℕ)
    (A : Fin 2 → CArr) (c : Fin 2) : CArr :=
  fun m' γ p _ => chartCoef M N Ψ K A c m' γ p

theorem sum_swap4 (K K' : ℕ) (T : (m : ℕ) → DerivativeWord2 m → (m' : ℕ) → DerivativeWord2 m' → ℝ) :
    ∑ m ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 m, ∑ m' ∈ Finset.range (K' + 1),
      ∑ γ : DerivativeWord2 m', T m α m' γ =
    ∑ m' ∈ Finset.range (K' + 1), ∑ γ : DerivativeWord2 m', ∑ m ∈ Finset.range (K + 1),
      ∑ α : DerivativeWord2 m, T m α m' γ := by
  calc _ = ∑ m ∈ Finset.range (K + 1), ∑ m' ∈ Finset.range (K' + 1), ∑ α : DerivativeWord2 m,
        ∑ γ : DerivativeWord2 m', T m α m' γ :=
        Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ m ∈ Finset.range (K + 1), ∑ m' ∈ Finset.range (K' + 1), ∑ γ : DerivativeWord2 m',
        ∑ α : DerivativeWord2 m, T m α m' γ :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => Finset.sum_comm
    _ = ∑ m' ∈ Finset.range (K' + 1), ∑ m ∈ Finset.range (K + 1), ∑ γ : DerivativeWord2 m',
        ∑ α : DerivativeWord2 m, T m α m' γ := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun m' _ => Finset.sum_comm

/-- **The transformed operator on one component.** For smooth `f`, `Ψ`, and `Ψ (N p) = p`. -/
theorem chart_apply (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) {N Ψ : Vec 2 → Vec 2}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (K : ℕ) (A : Fin 2 → CArr) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : Fin 2) (p : Vec 2) (hp : Ψ (N p) = p) :
    ∑ k : Fin 2, M p c k * applyArr K (A k) (fun y => f (Ψ y)) (N p) 0 =
      applyArr K (chartArr M N Ψ K A c) f p 0 := by
  have h1 : ∀ k : Fin 2, applyArr K (A k) (fun y => f (Ψ y)) (N p) 0 =
      ∑ m ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 m, ∑ m' ∈ Finset.range (K + 1),
        ∑ γ : DerivativeWord2 m', A k m α (N p) 0 * (fdbArr Ψ α m' γ (N p) 0 *
          orderedDerivative γ f p) := by
    intro k
    unfold applyArr
    refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun α _ => ?_
    have hmK : m ≤ K := by simpa [Nat.lt_succ_iff] using hm
    rw [orderedDerivative_comp_fdb hf hΨ α (N p), hp, Finset.mul_sum]
    -- extend the sum over m' from `m` to `K`
    have := Finset.sum_subset (Finset.range_subset_range.mpr (by omega : m + 1 ≤ K + 1))
      (f := fun m' => ∑ γ : DerivativeWord2 m', A k m α (N p) 0 * (fdbArr Ψ α m' γ (N p) 0 *
          orderedDerivative γ f p)) (fun m' hm' hm'' => by
        have : m < m' := by simp at hm' hm''; omega
        exact Finset.sum_eq_zero fun γ _ => by rw [arrSupp_fdbArr Ψ α m' this γ]; simp)
    rw [← this]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [Finset.mul_sum]
  have h2 : ∀ k : Fin 2, ∑ m ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 m,
      ∑ m' ∈ Finset.range (K + 1), ∑ γ : DerivativeWord2 m',
        A k m α (N p) 0 * (fdbArr Ψ α m' γ (N p) 0 * orderedDerivative γ f p) =
      ∑ m' ∈ Finset.range (K + 1), ∑ γ : DerivativeWord2 m',
        (∑ m ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 m,
          A k m α (N p) 0 * fdbArr Ψ α m' γ (N p) 0) * orderedDerivative γ f p := by
    intro k
    rw [sum_swap4 K K (fun m α m' γ =>
      A k m α (N p) 0 * (fdbArr Ψ α m' γ (N p) 0 * orderedDerivative γ f p))]
    refine Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun α _ => by ring
  simp_rw [h1, h2]
  unfold applyArr chartArr chartCoef
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun α _ => ?_
  ring

/-- **Push of an array flux operator** by a chart germ `Ψ` with inverse `Ψinv`: an array operator,
component by component. -/
theorem pushFlux_applyArr {Ψ Ψinv : Vec 2 → Vec 2} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hinv : ∀ x, Ψ (Ψinv x) = x) (K : ℕ) (A : Fin 2 → CArr) {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) (c : Fin 2) :
    pushFlux Ψ Ψinv (fun g y k => applyArr K (A k) g y 0) f x c =
      applyArr K (chartArr (fun p => jacMatrix Ψ (Ψinv p)) Ψinv Ψ K A c) f x 0 := by
  unfold pushFlux
  simp only [Matrix.mulVec, dotProduct]
  exact chart_apply (fun p => jacMatrix Ψ (Ψinv p)) hΨ K A hf c x (hinv x)

/-- **Pull of an array flux operator** by a chart germ `Φ` with inverse `Φinv`. -/
theorem pullFlux_applyArr {Φ Φinv : Vec 2 → Vec 2} (hΦinv : ContDiff ℝ (⊤ : ℕ∞) Φinv)
    (hinv : ∀ y, Φinv (Φ y) = y) (K : ℕ) (B : Fin 2 → CArr) {u : Vec 2 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (y : Vec 2) (c : Fin 2) :
    pullFlux Φ Φinv (fun g x k => applyArr K (B k) g x 0) u y c =
      applyArr K (chartArr (fun p => (jacMatrix Φ p)⁻¹) Φ Φinv K B c) u y 0 := by
  unfold pullFlux
  simp only [Matrix.mulVec, dotProduct]
  exact chart_apply (fun p => (jacMatrix Φ p)⁻¹) hΦinv K B hu c y (hinv y)

end AVRegularity.Providers.GenSem
end
