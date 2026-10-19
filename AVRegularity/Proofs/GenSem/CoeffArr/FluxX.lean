-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.CoeffArr.Mean

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Providers.GenSem

/-! The operators `D_{ε,i}` and `D_ε^α` on applied fields, and their polynomial dependence on `ε`.

`D_{ε,i} (applyArr K A a) = applyArr (K+1) (fastArr i A + (√η ε) • slowArr i A)`. The `ε`-dependence
is tracked by graded arrays `P : ℕ → CArr` (the coefficient of `ε^p`), evaluated by `evalG`;
`dG s i` is the graded version of `D_{ε,i}` (with `s = √η`) and `dWordG` its word iterate. -/

/-! ### Componentwise partials of vector fields -/

theorem slowPartial_pi_apply {ι : Type*} [Fintype ι] (Ψ : Vec 2 → Vec 2 → (ι → ℝ)) (j : Fin 2)
    (hΨ : ∀ z v, Differentiable ℝ (fun X => Ψ X z v)) (X z : Vec 2) (v : ι) :
    slowPartial j Ψ X z v = slowPartial j (fun X z => Ψ X z v) X z := by
  unfold slowPartial
  have hd : Differentiable ℝ (fun X' => Ψ X' z) := differentiable_pi.2 (hΨ z)
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) v).hasFDerivAt
    (x := Ψ X z)).comp X (hd X).hasFDerivAt
  have h2 : fderiv ℝ (fun X' => Ψ X' z v) X = _ := h.fderiv
  rw [h2]
  rfl

theorem fastPartial_pi_apply {ι : Type*} [Fintype ι] (Ψ : Vec 2 → Vec 2 → (ι → ℝ)) (j : Fin 2)
    (hΨ : ∀ X v, Differentiable ℝ (fun z => Ψ X z v)) (X z : Vec 2) (v : ι) :
    fastPartial j Ψ X z v = fastPartial j (fun X z => Ψ X z v) X z := by
  unfold fastPartial
  have hd : Differentiable ℝ (fun z' => Ψ X z') := differentiable_pi.2 (hΨ X)
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) v).hasFDerivAt
    (x := Ψ X z)).comp z (hd z).hasFDerivAt
  have h2 : fderiv ℝ (fun z' => Ψ X z' v) z = _ := h.fderiv
  rw [h2]
  rfl

/-! ### Differentiability of applied fields -/

theorem differentiable_applyArr_slow (K : ℕ) {A : CArr} (a : Vec 2 → ℝ)
    (ha : ContDiff ℝ ((K + 1 : ℕ) : WithTop ℕ∞) a) (hA : ArrSlowSmooth 1 A) (z : Vec 2) :
    Differentiable ℝ (fun X => applyArr K A a X z) := by
  unfold applyArr
  refine Differentiable.fun_sum fun m hm => Differentiable.fun_sum fun α _ => ?_
  have hm' : m ≤ K := by simpa [Nat.lt_succ_iff] using hm
  exact ((hA m α z).differentiable (by simp)).mul
    (orderedDerivative_differentiable α (ha.of_le (by exact_mod_cast (by omega : 1 + m ≤ K + 1))))

theorem differentiable_applyArr_fast (K : ℕ) {A : CArr} (a : Vec 2 → ℝ) (hA : ArrSmooth 1 A)
    (X : Vec 2) : Differentiable ℝ (fun z => applyArr K A a X z) := by
  unfold applyArr
  exact Differentiable.fun_sum fun m _ => Differentiable.fun_sum fun α _ =>
    (hA.diff_z m α X).mul_const _

/-! ### One letter -/

/-- The array of `D_{ε,i}` with `s = √η ε`. -/
def dArr (s : ℝ) (i : Fin 2) (A : CArr) : CArr := fastArr i A + s • slowArr i A

theorem dEps_applyArr (η ε : ℝ) (i : Fin 2) (K : ℕ) {A : CArr} (a : Vec 2 → ℝ)
    (ha : ContDiff ℝ ((K + 1 : ℕ) : WithTop ℕ∞) a) (hA : ArrSmooth 1 A) (hs : ArrSupp K A) :
    dEps η ε i (applyArr K A a) = applyArr (K + 1) (dArr (Real.sqrt η * ε) i A) a := by
  have hf : fastPartial i (applyArr K A a) = applyArr (K + 1) (fastArr i A) a := by
    rw [fastPartial_applyArr K A a i (fun m α X => hA.diff_z m α X)]
    exact (applyArr_eq_of_supp (Nat.le_succ K) (arrSupp_fastArr i hs) a).symm
  have hsl := slowPartial_applyArr K A a i ha hA.slow hs
  funext X z
  unfold dEps dArr
  rw [hf, hsl, applyArr_add, applyArr_smul]
  rfl

theorem dEps_pi_apply {ι : Type*} [Fintype ι] (η ε : ℝ) (i : Fin 2) (Ψ : Vec 2 → Vec 2 → (ι → ℝ))
    (hX : ∀ z v, Differentiable ℝ (fun X => Ψ X z v))
    (hZ : ∀ X v, Differentiable ℝ (fun z => Ψ X z v)) (X z : Vec 2) (v : ι) :
    dEps η ε i Ψ X z v = dEps η ε i (fun X z => Ψ X z v) X z := by
  unfold dEps
  show fastPartial i Ψ X z v + (Real.sqrt η * ε) * slowPartial i Ψ X z v = _
  rw [fastPartial_pi_apply Ψ i hZ, slowPartial_pi_apply Ψ i hX]
  rfl

theorem dEps_vec_applyArr {ι : Type*} [Fintype ι] (η ε : ℝ) (i : Fin 2) (K : ℕ) {B : ι → CArr}
    (a : Vec 2 → ℝ) (ha : ContDiff ℝ ((K + 1 : ℕ) : WithTop ℕ∞) a) (hA : ∀ v, ArrSmooth 1 (B v))
    (hs : ∀ v, ArrSupp K (B v)) :
    dEps η ε i (fun X z v => applyArr K (B v) a X z) =
      fun X z v => applyArr (K + 1) (dArr (Real.sqrt η * ε) i (B v)) a X z := by
  funext X z v
  rw [dEps_pi_apply η ε i _ (fun z v => differentiable_applyArr_slow K a ha (hA v).slow z)
    (fun X v => differentiable_applyArr_fast K a (hA v) X)]
  exact congrFun (congrFun (dEps_applyArr η ε i K a ha (hA v) (hs v)) X) z

/-! ### Graded arrays -/

/-- The graded version of `D_{ε,i}`, `s = √η`: the coefficient of `ε^p`. -/
def dG (s : ℝ) (i : Fin 2) (P : ℕ → CArr) : ℕ → CArr
  | 0 => fastArr i (P 0)
  | p + 1 => fastArr i (P (p + 1)) + s • slowArr i (P p)

/-- Evaluation `∑_{p < N} ε^p P_p` of a graded array. -/
def evalG (N : ℕ) (ε : ℝ) (P : ℕ → CArr) : CArr := ∑ p ∈ Finset.range N, ε ^ p • P p

/-- A graded array supported on orders `K + p` in grade `p` and on grades `< N`. -/
def GSupp (K N : ℕ) (P : ℕ → CArr) : Prop :=
  (∀ p, ArrSupp (K + p) (P p)) ∧ ∀ p, N ≤ p → P p = 0

/-- Each grade is `C^r` jointly. -/
def GSmooth (r : ℕ) (P : ℕ → CArr) : Prop := ∀ p, ArrSmooth r (P p)

/-- The graded array concentrated in grade `0`. -/
def constG (A : CArr) : ℕ → CArr := fun p => if p = 0 then A else 0

theorem slowArr_zero (j : Fin 2) : slowArr j 0 = 0 := by
  funext m β X z
  cases m <;> simp [slowArr, slowExtra, slowPartial]

theorem evalG_constG (ε : ℝ) (A : CArr) : evalG 1 ε (constG A) = A := by
  simp [evalG, constG]

theorem gSupp_constG {K : ℕ} {A : CArr} (hA : ArrSupp K A) : GSupp K 1 (constG A) := by
  refine ⟨fun p => ?_, fun p hp => ?_⟩
  · by_cases h : p = 0
    · subst h; simpa [constG] using hA
    · simp [constG, h, ArrSupp.zero]
  · simp [constG, show p ≠ 0 by omega]

theorem gSmooth_constG {r : ℕ} {A : CArr} (hA : ArrSmooth r A) : GSmooth r (constG A) := by
  intro p
  by_cases h : p = 0
  · subst h; simpa [constG] using hA
  · simp [constG, h, ArrSmooth.zero]

theorem gSupp_dG {K N : ℕ} {P : ℕ → CArr} (s : ℝ) (i : Fin 2) (hP : GSupp K N P) :
    GSupp K (N + 1) (dG s i P) := by
  refine ⟨fun p => ?_, fun p hp => ?_⟩
  · cases p with
    | zero => simpa [dG] using arrSupp_fastArr i (hP.1 0)
    | succ p =>
      simp only [dG]
      refine ArrSupp.add (arrSupp_fastArr i (hP.1 (p + 1))) (ArrSupp.smul s ?_)
      have := arrSupp_slowArr i (hP.1 p)
      rwa [show K + p + 1 = K + (p + 1) by omega] at this
  · cases p with
    | zero => omega
    | succ p =>
      simp [dG, hP.2 (p + 1) (by omega), hP.2 p (by omega), fastArr_zero, slowArr_zero]

theorem gSmooth_dG {r : ℕ} {P : ℕ → CArr} (s : ℝ) (i : Fin 2) (hP : GSmooth (r + 1) P) :
    GSmooth r (dG s i P) := by
  intro p
  cases p with
  | zero => exact arrSmooth_fastArr i (hP 0)
  | succ p =>
    exact (arrSmooth_fastArr i (hP (p + 1))).add ((arrSmooth_slowArr i (hP p)).smul s)

theorem gSupp_evalG {K N : ℕ} {P : ℕ → CArr} (ε : ℝ) (hP : GSupp K N P) :
    ArrSupp (K + N) (evalG N ε P) :=
  ArrSupp.sum _ fun p hp =>
    ((hP.1 p).mono (by simp at hp; omega)).smul _

theorem gSmooth_evalG {r : ℕ} {P : ℕ → CArr} (N : ℕ) (ε : ℝ) (hP : GSmooth r P) :
    ArrSmooth r (evalG N ε P) :=
  ArrSmooth.sum _ fun p _ => (hP p).smul _

theorem evalG_succ_of_zero {N : ℕ} {P : ℕ → CArr} (ε : ℝ) (hP : P N = 0) :
    evalG (N + 1) ε P = evalG N ε P := by
  simp [evalG, Finset.sum_range_succ, hP]

theorem dArr_evalG {N : ℕ} {P : ℕ → CArr} (s ε : ℝ) (i : Fin 2) (hP : GSmooth 1 P)
    (hz : ∀ p, N ≤ p → P p = 0) :
    dArr (s * ε) i (evalG N ε P) = evalG (N + 1) ε (dG s i P) := by
  unfold dArr evalG
  rw [fastArr_sum_smul i _ _ _ (fun p _ => hP p),
    slowArr_sum_smul i _ _ _ (fun p _ => (hP p).slow)]
  rw [Finset.sum_range_succ' _ N]
  simp only [dG, smul_add, Finset.sum_add_distrib]
  have h1 : ∑ p ∈ Finset.range N, ε ^ (p + 1) • fastArr i (P (p + 1)) + ε ^ 0 • fastArr i (P 0) =
      ∑ p ∈ Finset.range N, ε ^ p • fastArr i (P p) := by
    have := Finset.sum_range_succ' (fun p => ε ^ p • fastArr i (P p)) N
    rw [Finset.sum_range_succ, hz N le_rfl, fastArr_zero, smul_zero, add_zero] at this
    exact this.symm
  have h2 : ∑ p ∈ Finset.range N, ε ^ (p + 1) • s • slowArr i (P p) =
      (s * ε) • ∑ p ∈ Finset.range N, ε ^ p • slowArr i (P p) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_smul, smul_smul, pow_succ]
    congr 1
    ring
  rw [← h2, ← h1]
  abel

theorem dEps_vec_evalG {ι : Type*} [Fintype ι] (η ε : ℝ) (i : Fin 2) (K N : ℕ) {P : ι → ℕ → CArr}
    (a : Vec 2 → ℝ) (ha : ContDiff ℝ ((K + N + 1 : ℕ) : WithTop ℕ∞) a)
    (hS : ∀ v, GSmooth 1 (P v)) (hP : ∀ v, GSupp K N (P v)) :
    dEps η ε i (fun X z v => applyArr (K + N) (evalG N ε (P v)) a X z) =
      fun X z v => applyArr (K + (N + 1)) (evalG (N + 1) ε (dG (Real.sqrt η) i (P v))) a X z := by
  rw [dEps_vec_applyArr η ε i (K + N) a ha (fun v => gSmooth_evalG N ε (hS v))
    (fun v => gSupp_evalG ε (hP v))]
  funext X z v
  rw [dArr_evalG _ _ i (hS v) (fun p hp => (hP v).2 p hp)]
  rfl

/-! ### Words -/

/-- The graded version of `D_ε^α`. -/
def dWordG (s : ℝ) : (m : ℕ) → DerivativeWord2 m → (ℕ → CArr) → (ℕ → CArr)
  | 0, _, P => P
  | m + 1, α, P => dWordG s m (fun i => α i.succ) (dG s (α 0) P)

theorem dEpsWord_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η ε : ℝ) {m : ℕ}
    (α : DerivativeWord2 (m + 1)) (Ψ : Vec 2 → Vec 2 → E) :
    dEpsWord η ε α Ψ = dEpsWord η ε (fun i : Fin m => α i.succ) (dEps η ε (α 0) Ψ) := by
  simp [dEpsWord, List.ofFn_succ]

theorem dEpsWord_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η ε : ℝ)
    (α : DerivativeWord2 0) (Ψ : Vec 2 → Vec 2 → E) : dEpsWord η ε α Ψ = Ψ := by
  simp [dEpsWord]

theorem gSupp_dWordG {K : ℕ} (s : ℝ) : ∀ {m : ℕ} (α : DerivativeWord2 m) {N : ℕ} {P : ℕ → CArr},
    GSupp K N P → GSupp K (N + m) (dWordG s m α P) := by
  intro m
  induction m with
  | zero => intro α N P h; exact h
  | succ m ih =>
    intro α N P h
    have := ih (fun i => α i.succ) (gSupp_dG s (α 0) h)
    rwa [show N + 1 + m = N + (m + 1) by omega] at this

theorem gSmooth_dWordG {r : ℕ} (s : ℝ) : ∀ {m : ℕ} (α : DerivativeWord2 m) {P : ℕ → CArr},
    GSmooth (r + m) P → GSmooth r (dWordG s m α P) := by
  intro m
  induction m with
  | zero => intro α P h; exact h
  | succ m ih =>
    intro α P h
    exact ih (fun i => α i.succ) (gSmooth_dG (r := r + m) s (α 0) h)

theorem dEpsWord_vec_evalG {ι : Type*} [Fintype ι] (η ε : ℝ) (K : ℕ) {a : Vec 2 → ℝ} :
    ∀ {m : ℕ} (α : DerivativeWord2 m) (N : ℕ) {P : ι → ℕ → CArr},
    ContDiff ℝ ((K + N + m : ℕ) : WithTop ℕ∞) a → (∀ v, GSmooth m (P v)) →
    (∀ v, GSupp K N (P v)) →
    dEpsWord η ε α (fun X z v => applyArr (K + N) (evalG N ε (P v)) a X z) =
      fun X z v => applyArr (K + (N + m)) (evalG (N + m) ε (dWordG (Real.sqrt η) m α (P v))) a X z := by
  intro m
  induction m with
  | zero =>
    intro α N P _ _ _
    rw [dEpsWord_zero]
    rfl
  | succ m ih =>
    intro α N P ha hS hP
    have hS' : ∀ v, GSmooth 1 (P v) := fun v p => (hS v p).mono (by omega)
    rw [dEpsWord_succ, dEps_vec_evalG η ε (α 0) K N a
      (ha.of_le (by exact_mod_cast (by omega : K + N + 1 ≤ K + N + (m + 1)))) hS' hP]
    have := ih (fun i => α i.succ) (N + 1) (P := fun v => dG (Real.sqrt η) (α 0) (P v))
      (ha.of_le (by exact_mod_cast (by omega : K + (N + 1) + m ≤ K + N + (m + 1))))
      (fun v => gSmooth_dG (r := m) _ _ (hS v)) (fun v => gSupp_dG _ _ (hP v))
    rw [show N + 1 + m = N + (m + 1) by omega] at this
    exact this

/-! The cell operators `ℬ_1`, `ℬ_2` on applied fields, as applied arrays. -/

section
variable {ι : Type} [Fintype ι]

/-! ### Slow and fast partials of vector fields of applied arrays -/

theorem slowPartial_vec (j : Fin 2) (K : ℕ) {B : ι → CArr} {a : Vec 2 → ℝ}
    (ha : ContDiff ℝ ((K + 1 : ℕ) : WithTop ℕ∞) a) (hB : ∀ v, ArrSlowSmooth 1 (B v))
    (hs : ∀ v, ArrSupp K (B v)) :
    slowPartial j (fun X z v => applyArr K (B v) a X z) =
      fun X z v => applyArr (K + 1) (slowArr j (B v)) a X z := by
  funext X z v
  rw [slowPartial_pi_apply _ j (fun z v => differentiable_applyArr_slow K a ha (hB v) z)]
  exact congrFun (congrFun (slowPartial_applyArr K (B v) a j ha (hB v) (hs v)) X) z

theorem fastPartial_vec (j : Fin 2) (K : ℕ) {B : ι → CArr} {a : Vec 2 → ℝ}
    (hB : ∀ v, ArrSmooth 1 (B v)) :
    fastPartial j (fun X z v => applyArr K (B v) a X z) =
      fun X z v => applyArr K (fastArr j (B v)) a X z := by
  funext X z v
  rw [fastPartial_pi_apply _ j (fun X v => differentiable_applyArr_fast K a (hB v) X)]
  exact congrFun (congrFun (fastPartial_applyArr K (B v) a j (fun m α X => (hB v).diff_z m α X)) X) z

/-! ### `ℬ_1` -/

/-- The array of `ℬ_1` applied to a field with array `B`. -/
def cellB1Arr (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (vel : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (B : CArr) : CArr :=
  (∑ k : Fin 2, mulArr (fun _ z => Real.sqrt η * vel t z k) (slowArr k B)) +
    (-Real.sqrt η) • ∑ i : Fin 2, ∑ j : Fin 2,
      (mulArr (fun X _ => G t X i j) (fastArr i (slowArr j B)) +
        slowArr i (mulArr (fun X _ => G t X i j) (fastArr j B)))

/-- The array of `ℬ_2` applied to a field with array `B`. -/
def cellB2Arr (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ) (B : CArr) : CArr :=
  (-η) • ∑ i : Fin 2, ∑ j : Fin 2, slowArr i (mulArr (fun X _ => G t X i j) (slowArr j B))

theorem arrSupp_cellB1Arr {K : ℕ} {B : CArr} (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (vel : ℝ → Vec 2 → Vec 2) (t : ℝ) (hB : ArrSupp K B) :
    ArrSupp (K + 1) (cellB1Arr η G vel t B) := by
  have h1 : ∀ j, ArrSupp (K + 1) (slowArr j B) := fun j => arrSupp_slowArr j hB
  have h2 : ∀ j, ArrSupp K (fastArr j B) := fun j => arrSupp_fastArr j hB
  refine ArrSupp.add (ArrSupp.sum _ fun k _ => arrSupp_mulArr _ (h1 k))
    (ArrSupp.smul _ (ArrSupp.sum _ fun i _ => ArrSupp.sum _ fun j _ => ArrSupp.add
      (arrSupp_mulArr _ (arrSupp_fastArr i (h1 j))) (arrSupp_slowArr _ (arrSupp_mulArr _ (h2 j)))))

theorem arrSupp_cellB2Arr {K : ℕ} {B : CArr} (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (t : ℝ) (hB : ArrSupp K B) : ArrSupp (K + 2) (cellB2Arr η G t B) := by
  refine ArrSupp.smul _ (ArrSupp.sum _ fun i _ => ArrSupp.sum _ fun j _ => ?_)
  exact arrSupp_slowArr _ (arrSupp_mulArr _ (arrSupp_slowArr j hB))

theorem arrSmooth_cellB1Arr {r : ℕ} {B : CArr} (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (vel : ℝ → Vec 2 → Vec 2) (t : ℝ) (hB : ArrSmooth (r + 2) B)
    (hG : ∀ i j, ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => G t p.1 i j))
    (hv : ∀ k, ContDiff ℝ (r : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => vel t p.2 k)) :
    ArrSmooth r (cellB1Arr η G vel t B) := by
  have hB1 : ArrSmooth (r + 1 + 1) B := hB
  have hs : ∀ j, ArrSmooth (r + 1) (slowArr j B) := fun j => arrSmooth_slowArr j hB1
  have hf : ∀ j, ArrSmooth (r + 1) (fastArr j B) := fun j => arrSmooth_fastArr j hB1
  refine ArrSmooth.add (ArrSmooth.sum _ fun k _ => arrSmooth_mulArr (r := r) ?_ ?_)
    (ArrSmooth.smul _ (ArrSmooth.sum _ fun i _ => ArrSmooth.sum _ fun j _ => ArrSmooth.add ?_ ?_))
  · exact contDiff_const.mul (hv k)
  · exact ((hs k).mono (Nat.le_succ r))
  · exact arrSmooth_mulArr (hG i j |>.of_le (by exact_mod_cast Nat.le_succ r))
      (arrSmooth_fastArr i (hs j))
  · exact arrSmooth_slowArr i (arrSmooth_mulArr (hG i j) (hf j))

theorem arrSmooth_cellB2Arr {r : ℕ} {B : CArr} (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (t : ℝ) (hB : ArrSmooth (r + 2) B)
    (hG : ∀ i j, ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => G t p.1 i j)) :
    ArrSmooth r (cellB2Arr η G t B) := by
  have hB1 : ArrSmooth (r + 1 + 1) B := hB
  refine ArrSmooth.smul _ (ArrSmooth.sum _ fun i _ => ArrSmooth.sum _ fun j _ => ?_)
  exact arrSmooth_slowArr i (arrSmooth_mulArr (hG i j) (arrSmooth_slowArr j hB1))

/-- **`ℬ_1` of an applied field is an applied array.** -/
theorem cellB1_apply (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (vel : ℝ → Vec 2 → Vec 2)
    (t : ℝ) {K : ℕ} {B : ι → CArr} {a : Vec 2 → ℝ}
    (ha : ContDiff ℝ ((K + 1 : ℕ) : WithTop ℕ∞) a) (hB : ∀ v, ArrSmooth 2 (B v))
    (hs : ∀ v, ArrSupp K (B v))
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ) (fun p : Vec 2 × Vec 2 => G t p.1 i j)) (X z : Vec 2) (v : ι) :
    cellB1 η G vel t (fun X z v => applyArr K (B v) a X z) X z v =
      applyArr (K + 1) (cellB1Arr η G vel t (B v)) a X z := by
  have hB1 : ∀ v, ArrSmooth (1 + 1) (B v) := hB
  have hsl : ∀ j, slowPartial j (fun X z v => applyArr K (B v) a X z) =
      fun X z v => applyArr (K + 1) (slowArr j (B v)) a X z := fun j =>
    slowPartial_vec j K ha (fun v => (hB v).slow.mono (by omega)) hs
  have hfa : ∀ j, fastPartial j (fun X z v => applyArr K (B v) a X z) =
      fun X z v => applyArr K (fastArr j (B v)) a X z := fun j =>
    fastPartial_vec j K (fun v => (hB v).mono (by omega))
  have e1 : ∀ k, slowPartial k (fun X z v => applyArr K (B v) a X z) X z v =
      applyArr (K + 1) (slowArr k (B v)) a X z := fun k => by rw [hsl k]
  have e2 : ∀ i j, fastPartial i (slowPartial j (fun X z v => applyArr K (B v) a X z)) X z v =
      applyArr (K + 1) (fastArr i (slowArr j (B v))) a X z := fun i j => by
    rw [hsl j, fastPartial_vec i (K + 1) (fun v => arrSmooth_slowArr j (hB1 v))]
  have e4 : ∀ i j, slowPartial i (fun X' z' => G t X' i j •
      fastPartial j (fun X z v => applyArr K (B v) a X z) X' z') X z v =
      applyArr (K + 1) (slowArr i (mulArr (fun X _ => G t X i j) (fastArr j (B v)))) a X z := by
    intro i j
    have : (fun X' z' => G t X' i j • fastPartial j (fun X z v => applyArr K (B v) a X z) X' z') =
        fun X z v => applyArr K (mulArr (fun X _ => G t X i j) (fastArr j (B v))) a X z := by
      funext X z v
      rw [hfa j, applyArr_mulArr]
      rfl
    rw [this, slowPartial_vec i K ha (fun v => ?_) (fun v => ?_)]
    · exact (arrSmooth_mulArr (hG i j) (arrSmooth_fastArr j (hB1 v))).slow
    · exact arrSupp_mulArr _ (arrSupp_fastArr j (hs v))
  unfold cellB1
  simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, Pi.add_apply, smul_eq_mul, e1, e2, e4]
  unfold cellB1Arr
  simp only [applyArr_add, applyArr_smul, applyArr_sum, applyArr_mulArr, Pi.add_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [sub_eq_add_neg, neg_mul, Finset.mul_sum]

/-- **`ℬ_2` of an applied field is an applied array.** -/
theorem cellB2_apply (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ) {K : ℕ}
    {B : ι → CArr} {a : Vec 2 → ℝ} (ha : ContDiff ℝ ((K + 2 : ℕ) : WithTop ℕ∞) a)
    (hB : ∀ v, ArrSmooth 2 (B v)) (hs : ∀ v, ArrSupp K (B v))
    (hG : ∀ i j, ContDiff ℝ (1 : ℕ) (fun p : Vec 2 × Vec 2 => G t p.1 i j)) (X z : Vec 2) (v : ι) :
    cellB2 η G t (fun X z v => applyArr K (B v) a X z) X z v =
      applyArr (K + 2) (cellB2Arr η G t (B v)) a X z := by
  have hB1 : ∀ v, ArrSmooth (1 + 1) (B v) := hB
  have ha1 : ContDiff ℝ ((K + 1 : ℕ) : WithTop ℕ∞) a :=
    ha.of_le (by exact_mod_cast (by omega : K + 1 ≤ K + 2))
  have hsl : ∀ j, slowPartial j (fun X z v => applyArr K (B v) a X z) =
      fun X z v => applyArr (K + 1) (slowArr j (B v)) a X z := fun j =>
    slowPartial_vec j K ha1 (fun v => (hB v).slow.mono (by omega)) hs
  have e : ∀ i j, slowPartial i (fun X' z' => G t X' i j •
      slowPartial j (fun X z v => applyArr K (B v) a X z) X' z') X z v =
      applyArr (K + 2) (slowArr i (mulArr (fun X _ => G t X i j) (slowArr j (B v)))) a X z := by
    intro i j
    have : (fun X' z' => G t X' i j • slowPartial j (fun X z v => applyArr K (B v) a X z) X' z') =
        fun X z v => applyArr (K + 1) (mulArr (fun X _ => G t X i j) (slowArr j (B v))) a X z := by
      funext X z v
      rw [hsl j, applyArr_mulArr]
      rfl
    rw [this, slowPartial_vec i (K + 1) ha (fun v => ?_) (fun v => ?_)]
    · exact (arrSmooth_mulArr (hG i j) (arrSmooth_slowArr j (hB1 v))).slow
    · exact arrSupp_mulArr _ (arrSupp_slowArr j (hs v))
  unfold cellB2
  simp only [Pi.neg_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, e]
  unfold cellB2Arr
  simp only [applyArr_smul, applyArr_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [neg_mul, Finset.mul_sum]
end

/-! The flux, the source operator `𝒮_ε` and its Taylor coefficients `𝒮_j` on applied fields
with scalar fibres. -/

section
/-! ### Graded arrays as modules -/

/-- Graded arrays with each grade `C^r`, as a submodule. -/
def gSmoothSub (r : ℕ) : Submodule ℝ (ℕ → CArr) where
  carrier := {P | GSmooth r P}
  add_mem' := fun ha hb p => (ha p).add (hb p)
  zero_mem' := fun _ => ArrSmooth.zero r
  smul_mem' := fun c _ hP p => (hP p).smul c

/-- Graded arrays supported as in `GSupp`, as a submodule. -/
def gSuppSub (K N : ℕ) : Submodule ℝ (ℕ → CArr) where
  carrier := {P | GSupp K N P}
  add_mem' := fun ha hb =>
    ⟨fun p => (ha.1 p).add (hb.1 p), fun p hp => by simp [ha.2 p hp, hb.2 p hp]⟩
  zero_mem' := ⟨fun _ => ArrSupp.zero _, fun _ _ => rfl⟩
  smul_mem' := fun c _ hP =>
    ⟨fun p => (hP.1 p).smul c, fun p hp => by simp [hP.2 p hp]⟩

theorem GSupp.mono {K N N' : ℕ} (h : N ≤ N') {P : ℕ → CArr} (hP : GSupp K N P) :
    GSupp K N' P :=
  ⟨hP.1, fun p hp => hP.2 p (by omega)⟩

/-- Multiplication of every grade by a function of `(X,z)`. -/
def mulG (g : Vec 2 → Vec 2 → ℝ) (P : ℕ → CArr) : ℕ → CArr := fun p => mulArr g (P p)

theorem gSupp_mulG {K N : ℕ} {P : ℕ → CArr} (g : Vec 2 → Vec 2 → ℝ) (hP : GSupp K N P) :
    GSupp K N (mulG g P) :=
  ⟨fun p => arrSupp_mulArr g (hP.1 p), fun p hp => by
    funext m α X z; simp [mulG, mulArr, hP.2 p hp]⟩

theorem gSmooth_mulG {r : ℕ} {P : ℕ → CArr} {g : Vec 2 → Vec 2 → ℝ}
    (hg : ContDiff ℝ (r : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => g p.1 p.2)) (hP : GSmooth r P) :
    GSmooth r (mulG g P) :=
  fun p => arrSmooth_mulArr hg (hP p)

theorem mulArr_evalG (g : Vec 2 → Vec 2 → ℝ) (N : ℕ) (ε : ℝ) (P : ℕ → CArr) :
    mulArr g (evalG N ε P) = evalG N ε (mulG g P) := by
  funext m α X z
  simp [mulArr, evalG, mulG, Finset.sum_apply, Finset.mul_sum, mul_left_comm]

theorem evalG_eq_of_zero {N N' : ℕ} (h : N ≤ N') {P : ℕ → CArr} (ε : ℝ)
    (hP : ∀ p, N ≤ p → P p = 0) : evalG N' ε P = evalG N ε P := by
  induction N', h using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [evalG_succ_of_zero ε (hP n hn), ih]

/-- The additive map `P ↦ (applyArr K (evalG N ε P) a)(X,z)`. -/
def evalApplyHom (K N : ℕ) (ε : ℝ) (a : Vec 2 → ℝ) (X z : Vec 2) : (ℕ → CArr) →+ ℝ where
  toFun P := applyArr K (evalG N ε P) a X z
  map_zero' := by simp [evalG, applyArr]
  map_add' P Q := by
    simp [evalG, applyArr, smul_add, Finset.sum_add_distrib, add_mul]

theorem evalApplyHom_apply (K N : ℕ) (ε : ℝ) (a : Vec 2 → ℝ) (X z : Vec 2) (P : ℕ → CArr) :
    evalApplyHom K N ε a X z P = applyArr K (evalG N ε P) a X z := rfl

/-! ### The flux -/

variable {ι : Type} [Fintype ι] {Dm : ℕ}

/-- `f 1`-multiplication form of a scalar continuous linear map. -/
theorem clm_real_apply (f : ℝ →L[ℝ] ℝ) (x : ℝ) : f x = x * f 1 := by
  have := f.map_smul x 1
  simpa using this

/-- The graded array of one flux word. -/
def wordG (s : ℝ) (g : Vec 2 → Vec 2 → ℝ) (m : ℕ) (α : DerivativeWord2 m) (A : CArr) :
    ℕ → CArr :=
  mulG g (dWordG s m α (constG A))

/-- The graded coefficient array of the flux component `k`, component `v`, for the field with
component arrays
`A u`. -/
def fluxG (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (s t : ℝ) (k : Fin 2) (A : ι → CArr)
    (v : ι) : ℕ → CArr :=
  ∑ u : ι, ∑ d : Finset.Icc 2 Dm, ((edge v u d).map fun γ =>
    ∑ α : DerivativeWord2 (d.1 - 1),
      wordG s (fun X z => γ.coeff α t X z k * γ.map 1) (d.1 - 1) α (A u)).sum

theorem dEpsWord_component (η ε : ℝ) {K : ℕ} {A : ι → CArr} {a : Vec 2 → ℝ} {m : ℕ}
    (α : DerivativeWord2 m) (ha : ContDiff ℝ ((K + 1 + m : ℕ) : WithTop ℕ∞) a)
    (hA : ∀ v, ArrSmooth m (A v)) (hs : ∀ v, ArrSupp K (A v)) (X z : Vec 2) (u : ι) :
    dEpsWord η ε α (fun X z v => applyArr K (A v) a X z) X z u =
      applyArr (K + (1 + m)) (evalG (1 + m) ε (dWordG (Real.sqrt η) m α (constG (A u)))) a X z := by
  have h0 : (fun X z v => applyArr K (A v) a X z) =
      fun X z v => applyArr (K + 1) (evalG 1 ε (constG (A v))) a X z := by
    funext X z v
    rw [evalG_constG]
    exact (congrFun (congrFun (applyArr_eq_of_supp (Nat.le_succ K) (hs v) a) X) z).symm
  rw [h0, dEpsWord_vec_evalG η ε K α 1 (P := fun v => constG (A v)) ha
    (fun v => gSmooth_constG (hA v)) (fun v => gSupp_constG (hs v))]

theorem gSupp_wordG {K m : ℕ} {A : CArr} (hA : ArrSupp K A) (s : ℝ) (g : Vec 2 → Vec 2 → ℝ)
    (α : DerivativeWord2 m) : GSupp K (1 + m) (wordG s g m α A) :=
  gSupp_mulG g (gSupp_dWordG s α (gSupp_constG hA))

theorem gSmooth_wordG {r m : ℕ} {A : CArr} (hA : ArrSmooth (r + m) A) (s : ℝ)
    {g : Vec 2 → Vec 2 → ℝ}
    (hg : ContDiff ℝ (r : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => g p.1 p.2))
    (α : DerivativeWord2 m) : GSmooth r (wordG s g m α A) :=
  gSmooth_mulG hg (gSmooth_dWordG s α (gSmooth_constG hA))

/-- One word term of the flux, as an applied array. -/
theorem word_term (η ε : ℝ) {K Dm : ℕ} {A : ι → CArr} {a : Vec 2 → ℝ} {m : ℕ}
    (hm : 1 + m ≤ Dm) (α : DerivativeWord2 m) (g : Vec 2 → Vec 2 → ℝ)
    (ha : ContDiff ℝ ((K + Dm : ℕ) : WithTop ℕ∞) a)
    (hA : ∀ v, ArrSmooth m (A v)) (hs : ∀ v, ArrSupp K (A v)) (X z : Vec 2) (u : ι) :
    g X z * dEpsWord η ε α (fun X z v => applyArr K (A v) a X z) X z u =
      evalApplyHom (K + Dm) Dm ε a X z (wordG (Real.sqrt η) g m α (A u)) := by
  rw [dEpsWord_component η ε α (ha.of_le (by exact_mod_cast (by omega : K + 1 + m ≤ K + Dm))) hA hs,
    evalApplyHom_apply, wordG, ← mulArr_evalG, applyArr_mulArr]
  have hQ := gSupp_dWordG (Real.sqrt η) α (gSupp_constG (hs u))
  rw [evalG_eq_of_zero (N := 1 + m) hm ε hQ.2]
  have hsupp : ArrSupp (K + (1 + m)) (evalG (1 + m) ε (dWordG (Real.sqrt η) m α (constG (A u)))) :=
    gSupp_evalG ε hQ
  rw [show (K + Dm) = K + Dm from rfl,
    applyArr_eq_of_supp (K := K + (1 + m)) (K' := K + Dm) (by omega) hsupp]

theorem sourceFlux_apply (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (η ε t : ℝ) (k : Fin 2)
    {K : ℕ} {A : ι → CArr} {a : Vec 2 → ℝ} (ha : ContDiff ℝ ((K + Dm : ℕ) : WithTop ℕ∞) a)
    (hA : ∀ v, ArrSmooth Dm (A v)) (hs : ∀ v, ArrSupp K (A v)) (X z : Vec 2) (v : ι) :
    sourceFlux edge η ε t (fun X z v => applyArr K (A v) a X z) k X z v =
      evalApplyHom (K + Dm) Dm ε a X z (fluxG edge (Real.sqrt η) t k A v) := by
  unfold sourceFlux fluxG
  rw [map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun γ _ => ?_
  simp only [Function.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hd := d.2
  rw [Finset.mem_Icc] at hd
  have := word_term η ε (K := K) (A := A) (a := a) (m := d.1 - 1) (Dm := Dm) (by omega) α
    (fun X z => γ.coeff α t X z k * γ.map 1) ha (fun v => (hA v).mono (by omega)) hs X z u
  rw [← this, smul_eq_mul]
  change γ.coeff α t X z k * γ.map _ = _
  rw [clm_real_apply γ.map]
  ring
end

/-! `liftApply` of a single-component test field, and of a vector field of applied arrays, as
applied arrays. Scalar fibres. -/

section
variable {ι : Type}

/-! ### Ordered derivatives of vector fields -/

theorem orderedDerivative_zero_fun {m : ℕ} (α : DerivativeWord2 m) :
    orderedDerivative α (fun _ : Vec 2 => (0 : ℝ)) = fun _ => 0 := by
  induction m with
  | zero =>
    have : α = Fin.elim0 := Subsingleton.elim _ _
    subst this
    rw [orderedDerivative_zero_word]
  | succ m ih =>
    rw [orderedDerivative_succ]
    have : (fun x => fderiv ℝ (fun _ : Vec 2 => (0 : ℝ)) x (basisVec (α 0))) = fun _ => 0 := by
      funext x; simp
    rw [this, ih]

theorem orderedDerivative_pi_apply [Fintype ι] : ∀ {m : ℕ} (α : DerivativeWord2 m) {g : Vec 2 → (ι → ℝ)},
    (∀ u, ContDiff ℝ (m : WithTop ℕ∞) (fun X => g X u)) → ∀ (X : Vec 2) (u : ι),
    orderedDerivative α g X u = orderedDerivative α (fun X => g X u) X := by
  intro m
  induction m with
  | zero =>
    intro α g _ X u
    have : α = Fin.elim0 := Subsingleton.elim _ _
    subst this
    rw [orderedDerivative_zero_word, orderedDerivative_zero_word]
  | succ m ih =>
    intro α g hg X u
    have hd : Differentiable ℝ g := differentiable_pi.2 fun u => (hg u).differentiable (by simp)
    have hcomp : ∀ X u, fderiv ℝ g X (basisVec (α 0)) u =
        fderiv ℝ (fun X => g X u) X (basisVec (α 0)) := by
      intro X u
      have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) u).hasFDerivAt
        (x := g X)).comp X (hd X).hasFDerivAt
      have h2 : fderiv ℝ (fun X => g X u) X = _ := h.fderiv
      rw [h2]
      rfl
    have hg' : ∀ u, ContDiff ℝ (m : WithTop ℕ∞) (fun X => fderiv ℝ g X (basisVec (α 0)) u) := by
      intro u
      have : (fun X => fderiv ℝ g X (basisVec (α 0)) u) =
          fun X => fderiv ℝ (fun X => g X u) X (basisVec (α 0)) := funext fun X => hcomp X u
      rw [this]
      exact contDiff_dirDeriv_nat (hg u) _
    rw [orderedDerivative_succ, orderedDerivative_succ,
      ih (fun i => α i.succ) (g := fun x => fderiv ℝ g x (basisVec (α 0))) hg' X u]
    congr 1
    funext X
    exact hcomp X u

theorem orderedDerivative_single_apply {m : ℕ} (α : DerivativeWord2 m) [Fintype ι] [DecidableEq ι] (w : ι)
    {a : Vec 2 → ℝ} (ha : ContDiff ℝ (m : WithTop ℕ∞) a) (X : Vec 2) (u : ι) :
    orderedDerivative α (fun Y => (Pi.single w (a Y) : ι → ℝ)) X u =
      if u = w then orderedDerivative α a X else 0 := by
  rw [orderedDerivative_pi_apply α (fun u => ?_) X u]
  · by_cases h : u = w
    · subst h; simp
    · have : (fun Y => (Pi.single w (a Y) : ι → ℝ) u) = fun _ => (0 : ℝ) := by
        funext Y; simp [h]
      rw [this, orderedDerivative_zero_fun]
      simp [h]
  · by_cases h : u = w
    · subst h; simpa using ha
    · have : (fun Y => (Pi.single w (a Y) : ι → ℝ) u) = fun _ => (0 : ℝ) := by
        funext Y; simp [h]
      rw [this]
      exact contDiff_const

/-! ### `liftApply` -/

/-- The scalar coefficient array of the entry `(v ← w)` of an order-`k` lift coefficient. -/
def entryArr (c : LiftCoeff ι (fun _ => ℝ)) (k : ℕ) (w : ι) (t : ℝ) (v : ι) : CArr :=
  fun m α X z => if m ≤ k then c m α t X z v w 1 else 0

theorem arrSupp_entryArr (c : LiftCoeff ι (fun _ => ℝ)) (k : ℕ) (w : ι) (t : ℝ) (v : ι) :
    ArrSupp k (entryArr c k w t v) := by
  intro m hm α
  funext X z
  simp [entryArr, show ¬ m ≤ k by omega]

theorem arrSmooth_entryArr {r : ℕ} (c : LiftCoeff ι (fun _ => ℝ)) (k : ℕ) (w : ι) (t : ℝ) (v : ι)
    (h : ∀ m α, ContDiff ℝ (r : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => c m α t p.1 p.2 v w 1)) :
    ArrSmooth r (entryArr c k w t v) := by
  intro m α
  unfold entryArr
  by_cases hm : m ≤ k
  · simpa [hm] using h m α
  · simpa [hm] using contDiff_const

/-- `ℝ`-linear forms: `c x = x * c 1`. -/
theorem liftApply_single [Fintype ι] [DecidableEq ι] (k : ℕ) (c : LiftCoeff ι (fun _ => ℝ)) (w : ι)
    {a : Vec 2 → ℝ} (ha : ContDiff ℝ (k : WithTop ℕ∞) a) (t : ℝ) (X z : Vec 2) (v : ι) :
    liftApply k c (fun _ Y => (Pi.single w (a Y) : ι → ℝ)) t X z v =
      applyArr k (entryArr c k w t v) a X z := by
  unfold liftApply applyArr
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun α _ => ?_
  have hmk : m ≤ k := by simpa [Nat.lt_succ_iff] using hm
  have hso := orderedDerivative_single_apply α w (ha.of_le (by exact_mod_cast hmk)) X
  rw [Finset.sum_eq_single w]
  · rw [hso w]
    simp only [ite_true, entryArr, hmk]
    rw [show (c m α t X z v w) (orderedDerivative α a X) =
        orderedDerivative α a X * c m α t X z v w 1 from ?_]
    · ring
    · have := (c m α t X z v w).map_smul (orderedDerivative α a X) 1
      simpa using this
  · intro u _ hu
    rw [hso u]
    simp [hu]
  · intro h; exact absurd (Finset.mem_univ w) h

theorem contDiff_applyArr_slow (K r : ℕ) {B : CArr} {a : Vec 2 → ℝ}
    (ha : ContDiff ℝ ((K + r : ℕ) : WithTop ℕ∞) a) (hB : ArrSlowSmooth r B) (z : Vec 2) :
    ContDiff ℝ (r : WithTop ℕ∞) (fun X => applyArr K B a X z) := by
  unfold applyArr
  refine ContDiff.sum fun m hm => ContDiff.sum fun α _ => (hB m α z).mul ?_
  have hm' : m ≤ K := by simpa [Nat.lt_succ_iff] using hm
  exact contDiff_orderedDerivative_top (r := r) α
    (ha.of_le (by exact_mod_cast (by omega : r + m ≤ K + r)))

/-- The scalar coefficient array of the entry `(v ← u)` of a lift coefficient (no truncation). -/
def cArr (c : LiftCoeff ι (fun _ => ℝ)) (t : ℝ) (v u : ι) : CArr :=
  fun m α X z => c m α t X z v u 1

/-- **A lift coefficient applied to a vector field of applied arrays** (e.g. a cell mean) is a sum
of composed arrays. Only the value `L t` of the field matters. -/
theorem liftApply_arrField [Fintype ι] (J K : ℕ) (c : LiftCoeff ι (fun _ => ℝ)) (t : ℝ)
    (B : ι → CArr) {a : Vec 2 → ℝ} (z0 : Vec 2) (L : ℝ → Vec 2 → ι → ℝ)
    (hL : L t = fun X u => applyArr K (B u) a X z0)
    (ha : ContDiff ℝ ((K + J : ℕ) : WithTop ℕ∞) a) (hB : ∀ u, ArrSlowSmooth J (B u))
    (hs : ∀ u, ArrSupp K (B u)) (X z : Vec 2) (v : ι) :
    liftApply J c L t X z v =
      ∑ u : ι, applyArr (J + K) (compArr J (cArr c t v u) (B u) z0) a X z := by
  have hcomp : ∀ u, applyArr J (cArr c t v u) (fun X => applyArr K (B u) a X z0) X z =
      applyArr (J + K) (compArr J (cArr c t v u) (B u) z0) a X z := fun u =>
    congrFun (congrFun (applyArr_comp J K (cArr c t v u) (B u) a z0 ha (hB u) (hs u)) X) z
  simp_rw [← hcomp]
  unfold liftApply applyArr
  rw [hL]
  have hord : ∀ m ∈ Finset.range (J + 1), ∀ (α : DerivativeWord2 m) (u : ι),
      orderedDerivative α (fun X u => applyArr K (B u) a X z0) X u =
        orderedDerivative α (fun X => applyArr K (B u) a X z0) X := by
    intro m hm α u
    have hmJ : m ≤ J := by simpa [Nat.lt_succ_iff] using hm
    refine orderedDerivative_pi_apply α (fun u => ?_) X u
    exact (contDiff_applyArr_slow K m (ha.of_le (by exact_mod_cast (by omega : K + m ≤ K + J)))
      ((hB u).mono hmJ) z0)
  calc _ = ∑ m ∈ Finset.range (J + 1), ∑ α : DerivativeWord2 m, ∑ u : ι,
        cArr c t v u m α X z * orderedDerivative α (fun X => applyArr K (B u) a X z0) X := by
        refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun α _ =>
          Finset.sum_congr rfl fun u _ => ?_
        rw [hord m hm α u, clm_real_apply, mul_comm]
        rfl
    _ = ∑ m ∈ Finset.range (J + 1), ∑ u : ι, ∑ α : DerivativeWord2 m,
        cArr c t v u m α X z * orderedDerivative α (fun X => applyArr K (B u) a X z0) X :=
        Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = _ := Finset.sum_comm
end

/-! The source operator `𝒮_ε` and the Taylor coefficients `𝒮_j` of an applied field with scalar
fibres, as applied arrays. -/

section
variable {ι : Type} [Fintype ι] {Dm : ℕ}

/-- The graded coefficient array of `𝒮_ε Φ`, component `v`, for `Φ` with component arrays `A u`:
the grade `j` is the array of `𝒮_j`. -/
def sourceG (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (s t : ℝ) (A : ι → CArr) (v : ι) :
    ℕ → CArr :=
  ∑ k : Fin 2, dG s k (fluxG edge s t k A v)

theorem fluxG_gSupp (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (s t : ℝ) (k : Fin 2)
    {K : ℕ} {A : ι → CArr} (hs : ∀ v, ArrSupp K (A v)) (v : ι) :
    GSupp K Dm (fluxG edge s t k A v) := by
  unfold fluxG
  refine (gSuppSub K Dm).sum_mem fun u _ => (gSuppSub K Dm).sum_mem fun d _ =>
    (gSuppSub K Dm).list_sum_mem fun P hP => ?_
  obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hP
  refine (gSuppSub K Dm).sum_mem fun α _ => ?_
  have hd := d.2
  rw [Finset.mem_Icc] at hd
  exact (gSupp_wordG (hs u) s _ α).mono (by omega)

theorem fluxG_gSmooth (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (s t : ℝ) (k : Fin 2)
    {r : ℕ} {A : ι → CArr} (hA : ∀ v, ArrSmooth (r + Dm) (A v))
    (hE : ∀ (v u : ι) (d : Finset.Icc 2 Dm) (γ : Constituent d.1 ℝ ℝ), γ ∈ edge v u d →
      ∀ α, ContDiff ℝ (r : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => γ.coeff α t p.1 p.2 k)) (v : ι) :
    GSmooth r (fluxG edge s t k A v) := by
  unfold fluxG
  refine (gSmoothSub r).sum_mem fun u _ => (gSmoothSub r).sum_mem fun d _ =>
    (gSmoothSub r).list_sum_mem fun P hP => ?_
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hP
  refine (gSmoothSub r).sum_mem fun α _ => ?_
  have hd := d.2
  rw [Finset.mem_Icc] at hd
  exact gSmooth_wordG ((hA u).mono (by omega)) s ((hE v u d γ hγ α).mul contDiff_const) α

theorem sourceG_gSupp (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (s t : ℝ)
    {K : ℕ} {A : ι → CArr} (hs : ∀ v, ArrSupp K (A v)) (v : ι) :
    GSupp K (Dm + 1) (sourceG edge s t A v) :=
  (gSuppSub K (Dm + 1)).sum_mem fun k _ => gSupp_dG s k (fluxG_gSupp edge s t k hs v)

theorem sourceG_gSmooth (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (s t : ℝ)
    {A : ι → CArr} (r : ℕ) (hr : ∀ k v, GSmooth (r + 1) (fluxG edge s t k A v)) (v : ι) :
    GSmooth r (sourceG edge s t A v) :=
  (gSmoothSub r).sum_mem fun k _ => gSmooth_dG s k (hr k v)

theorem sourceOp_apply (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (η ε t : ℝ)
    {K : ℕ} {A : ι → CArr} {a : Vec 2 → ℝ}
    (ha : ContDiff ℝ ((K + Dm + 1 : ℕ) : WithTop ℕ∞) a)
    (hA : ∀ v, ArrSmooth (1 + Dm) (A v)) (hs : ∀ v, ArrSupp K (A v))
    (hE : ∀ (v u : ι) (d : Finset.Icc 2 Dm) (γ : Constituent d.1 ℝ ℝ), γ ∈ edge v u d →
      ∀ α k, ContDiff ℝ (1 : ℕ) (fun p : Vec 2 × Vec 2 => γ.coeff α t p.1 p.2 k))
    (X z : Vec 2) (v : ι) :
    sourceOp edge η ε t (fun X z v => applyArr K (A v) a X z) X z v =
      evalApplyHom (K + (Dm + 1)) (Dm + 1) ε a X z (sourceG edge (Real.sqrt η) t A v) := by
  have hflux : ∀ k, sourceFlux edge η ε t (fun X z v => applyArr K (A v) a X z) k =
      fun X z v => applyArr (K + Dm) (evalG Dm ε (fluxG edge (Real.sqrt η) t k A v)) a X z := by
    intro k
    funext X z v
    exact sourceFlux_apply edge η ε t k (ha.of_le (by exact_mod_cast (by omega : K + Dm ≤ K + Dm + 1)))
      (fun v => (hA v).mono (by omega)) hs X z v
  unfold sourceOp sourceG
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hflux k, dEps_vec_evalG η ε k K Dm a ha (fun v => fluxG_gSmooth edge _ t k hA (fun v u d γ hγ α =>
    hE v u d γ hγ α k) v) (fun v => fluxG_gSupp edge _ t k hs v)]
  rfl

theorem applyArr_evalG (K N : ℕ) (ε : ℝ) (P : ℕ → CArr) (a : Vec 2 → ℝ) (X z : Vec 2) :
    applyArr K (evalG N ε P) a X z = ∑ p ∈ Finset.range N, ε ^ p * applyArr K (P p) a X z := by
  unfold evalG
  rw [applyArr_sum]
  simp [applyArr_smul]

theorem iteratedDeriv_poly {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (N : ℕ)
    (w : ℕ → E) {j : ℕ} (hj : j < N) :
    iteratedDeriv j (fun ε : ℝ => ∑ p ∈ Finset.range N, ε ^ p • w p) 0 =
      (j.factorial : ℝ) • w j := by
  have hc : ∀ p, ContDiffAt ℝ (j : WithTop ℕ∞) (fun ε : ℝ => ε ^ p • w p) 0 := fun p =>
    ((contDiff_id.pow p).smul_const (w p)).contDiffAt
  have hc' : ∀ p, ContDiffAt ℝ (j : WithTop ℕ∞) (fun ε : ℝ => ε ^ p) 0 := fun p =>
    (contDiff_id.pow p).contDiffAt
  rw [iteratedDeriv_fun_sum (fun p _ => hc p)]
  have hterm : ∀ p, iteratedDeriv j (fun ε : ℝ => ε ^ p • w p) 0 =
      (if j = p then (p.factorial : ℝ) else 0) • w p := by
    intro p
    rw [iteratedDeriv_smul_const (hc' p), iteratedDeriv_fun_pow_zero]
    split_ifs <;> simp
  simp_rw [hterm]
  rw [Finset.sum_eq_single j]
  · simp
  · intro p _ hp
    simp [Ne.symm hp]
  · intro h
    exact absurd (Finset.mem_range.mpr hj) h

/-- **The Taylor coefficients `𝒮_j` of an applied field are applied arrays.** -/
theorem sourceCoeff_apply (edge : ConstituentEdges Dm (fun _ : ι => ℝ)) (η : ℝ) {j : ℕ}
    (hj : j ≤ Dm) (t : ℝ) {K : ℕ} {A : ι → CArr} {a : Vec 2 → ℝ}
    (ha : ContDiff ℝ ((K + Dm + 1 : ℕ) : WithTop ℕ∞) a)
    (hA : ∀ v, ArrSmooth (1 + Dm) (A v)) (hs : ∀ v, ArrSupp K (A v))
    (hE : ∀ (v u : ι) (d : Finset.Icc 2 Dm) (γ : Constituent d.1 ℝ ℝ), γ ∈ edge v u d →
      ∀ α k, ContDiff ℝ (1 : ℕ) (fun p : Vec 2 × Vec 2 => γ.coeff α t p.1 p.2 k))
    (X z : Vec 2) (v : ι) :
    sourceCoeff edge η j t (fun X z v => applyArr K (A v) a X z) X z v =
      applyArr (K + (Dm + 1)) (sourceG edge (Real.sqrt η) t A v j) a X z := by
  unfold sourceCoeff
  have hfun : (fun ε : ℝ => sourceOp edge η ε t (fun X z v => applyArr K (A v) a X z) X z) =
      fun ε => ∑ p ∈ Finset.range (Dm + 1), ε ^ p •
        (fun v => applyArr (K + (Dm + 1)) (sourceG edge (Real.sqrt η) t A v p) a X z) := by
    funext ε v
    rw [sourceOp_apply edge η ε t ha hA hs hE X z v, evalApplyHom_apply, applyArr_evalG]
    simp
  rw [hfun, iteratedDeriv_poly _ _ (Nat.lt_succ_of_le hj)]
  simp [Nat.factorial_ne_zero]
end

/-! The recursion source `A_n^{(hh)}` and the cell mean `L_n^{(hh)}` of the lift, for the test field
`fun _ Y => Pi.single w (a Y)` and scalar fibres, as applied arrays. -/

section
variable {ι : Type} {Dm : ℕ}

theorem applyArr_sub (K : ℕ) (A B : CArr) (a : Vec 2 → ℝ) :
    applyArr K (A - B) a = applyArr K A a - applyArr K B a := by
  funext X z
  simp only [applyArr, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem applyArr_neg (K : ℕ) (A : CArr) (a : Vec 2 → ℝ) :
    applyArr K (-A) a = -applyArr K A a := by
  funext X z
  simp only [applyArr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem ArrSmooth.sub {r : ℕ} {A B : CArr} (hA : ArrSmooth r A) (hB : ArrSmooth r B) :
    ArrSmooth r (A - B) := (arrSmoothSub r).sub_mem hA hB

theorem ArrSupp.sub {K : ℕ} {A B : CArr} (hA : ArrSupp K A) (hB : ArrSupp K B) :
    ArrSupp K (A - B) := (arrSuppSub K).sub_mem hA hB

theorem ArrSupp.neg {K : ℕ} {A : CArr} (hA : ArrSupp K A) : ArrSupp K (-A) :=
  (arrSuppSub K).neg_mem hA

theorem continuous_applyArr_z {K : ℕ} {A : CArr} (hA : ArrSmooth 0 A) (a : Vec 2 → ℝ) (X : Vec 2) :
    Continuous (fun z => applyArr K A a X z) := by
  unfold applyArr
  refine continuous_finsetSum _ fun m _ => continuous_finsetSum _ fun α _ => ?_
  exact ((hA.continuous m α).comp (continuous_const.prodMk continuous_id)).mul continuous_const

/-! ### Regularity bundle -/

/-- The regularity of the lift data at time `t` used by the array identities: all coefficients
involved in `liftCellSource Q Cc · hh n t` are jointly `C^R` in `(X,z)`. -/
structure LiftRegular (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) (t : ℝ) (hh n R : ℕ) : Prop where
  /-- The entries `(v ← w)` of the lift coefficients `Cc hh' k`, `hh' ≤ hh`, `k ≤ n`. -/
  coeff : ∀ hh' ≤ hh, ∀ k ≤ n, ∀ (m : ℕ) (α : DerivativeWord2 m) (v : ι),
    ContDiff ℝ (R : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => Cc hh' k m α t p.1 p.2 v w 1)
  /-- The metric. -/
  metric : ∀ i j, ContDiff ℝ (R : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => Q.G t p.1 i j)
  /-- The drift. -/
  drift : ∀ k, ContDiff ℝ (R : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => Q.v t p.2 k)
  /-- The source-edge coefficients. -/
  edge : ∀ (v u : ι) (d : Finset.Icc 2 Dm) (γ : Constituent d.1 ℝ ℝ), γ ∈ Q.edge v u d →
    ∀ α k, ContDiff ℝ (R : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => γ.coeff α t p.1 p.2 k)

theorem LiftRegular.mono {Q : LiftOperatorData ι (fun _ => ℝ) Dm}
    {Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)} {w : ι} {t : ℝ} {hh n R hh' n' R' : ℕ}
    (h : LiftRegular Q Cc w t hh n R) (h1 : hh' ≤ hh) (h2 : n' ≤ n) (h3 : R' ≤ R) :
    LiftRegular Q Cc w t hh' n' R' where
  coeff := fun a ha k hk m α v =>
    (h.coeff a (ha.trans h1) k (hk.trans h2) m α v).of_le (by exact_mod_cast h3)
  metric := fun i j => (h.metric i j).of_le (by exact_mod_cast h3)
  drift := fun k => (h.drift k).of_le (by exact_mod_cast h3)
  edge := fun v u d γ hγ α k => (h.edge v u d γ hγ α k).of_le (by exact_mod_cast h3)

/-! ### The array of `A_n^{(hh)}` -/

section

variable [Fintype ι]

/-- The coefficient array of the component `v` of `A_n^{(hh)} (single w a)`. -/
def liftAArr (Q : LiftOperatorData ι (fun _ => ℝ) Dm) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (w : ι) (hh n : ℕ) (t : ℝ) (v : ι) : CArr :=
  cellB1Arr Q.η Q.G Q.v t (entryArr (Cc hh (n - 1)) (n - 1) w t v)
    + (if 2 ≤ n then cellB2Arr Q.η Q.G t (entryArr (Cc hh (n - 2)) (n - 2) w t v) else 0)
    - (if hh = 0 then 0 else ∑ j ∈ Finset.range (min Dm n + 1),
        sourceG Q.edge (Real.sqrt Q.η) t (fun u => entryArr (Cc (hh - 1) (n - j)) (n - j) w t u) v j)

theorem arrSupp_liftAArr (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) (hh n : ℕ) (t : ℝ) (v : ι) :
    ArrSupp (n + 1) (liftAArr Q Cc w hh n t v) := by
  unfold liftAArr
  refine ArrSupp.sub (ArrSupp.add ?_ ?_) ?_
  · exact (arrSupp_cellB1Arr Q.η Q.G Q.v t (arrSupp_entryArr _ _ _ _ _)).mono (by omega)
  · split_ifs
    · exact (arrSupp_cellB2Arr Q.η Q.G t (arrSupp_entryArr _ _ _ _ _)).mono (by omega)
    · exact ArrSupp.zero _
  · split_ifs
    · exact ArrSupp.zero _
    · refine ArrSupp.sum _ fun j hj => ?_
      have hjn : j ≤ n := by
        have := Finset.mem_range.mp hj
        omega
      have := (sourceG_gSupp Q.edge (Real.sqrt Q.η) t
        (A := fun u => entryArr (Cc (hh - 1) (n - j)) (n - j) w t u)
        (fun u => arrSupp_entryArr _ _ _ _ _) v).1 j
      rw [show n - j + j = n by omega] at this
      exact this.mono (by omega)

theorem arrSmooth_liftAArr (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} {t : ℝ} {r : ℕ}
    (hreg : LiftRegular Q Cc w t hh n (r + Dm + 2)) (v : ι) :
    ArrSmooth r (liftAArr Q Cc w hh n t v) := by
  have hent : ∀ hh' k, hh' ≤ hh → k ≤ n → ∀ u,
      ArrSmooth (r + Dm + 2) (entryArr (Cc hh' k) k w t u) := fun hh' k h1 h2 u =>
    arrSmooth_entryArr _ _ _ _ _ (hreg.coeff hh' h1 k h2 · · u)
  have hG : ∀ i j, ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => Q.G t p.1 i j) :=
    fun i j => (hreg.metric i j).of_le (by exact_mod_cast (by omega : r + 1 ≤ r + Dm + 2))
  unfold liftAArr
  refine ArrSmooth.sub (ArrSmooth.add ?_ ?_) ?_
  · refine arrSmooth_cellB1Arr Q.η Q.G Q.v t ((hent _ _ le_rfl (by omega) v).mono (by omega)) hG
      (fun k => (hreg.drift k).of_le (by exact_mod_cast (by omega : r ≤ r + Dm + 2)))
  · split_ifs with h2
    · exact arrSmooth_cellB2Arr Q.η Q.G t ((hent _ _ le_rfl (by omega) v).mono (by omega)) hG
    · exact ArrSmooth.zero _
  · split_ifs with h0
    · exact ArrSmooth.zero _
    · refine ArrSmooth.sum _ fun j hj => ?_
      have hjn : j ≤ n := by
        have := Finset.mem_range.mp hj
        omega
      exact sourceG_gSmooth Q.edge (Real.sqrt Q.η) t r (fun k v' =>
        fluxG_gSmooth Q.edge _ t k (r := r + 1)
          (fun u => (hent (hh - 1) (n - j) (by omega) (by omega) u).mono (by omega))
          (fun v u d γ hγ α => (hreg.edge v u d γ hγ α k).of_le
            (by exact_mod_cast (by omega : r + 1 ≤ r + Dm + 2))) v') v j

end
end

/-! **The coefficient array of the slow flux `liftFluxX`.** For scalar fibres and the test
field `fun _ Y => Pi.single w (a Y)`, the component `v`, direction `κ` of `liftFluxX` is the applied
array `applyArr n (fluxXArr Q Cc w hh n t v κ) a` (see `liftFluxX_applyArr`). This file: the
definition, the support and the smoothness. -/

section
variable {ι : Type} [Fintype ι] {Dm : ℕ}

/-- The term `√η v_κ C_{n-1}` of the slow flux. -/
def fluxXA (Q : LiftOperatorData ι (fun _ => ℝ) Dm) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (w : ι) (hh n : ℕ) (t : ℝ) (v : ι) (κ : Fin 2) : CArr :=
  mulArr (fun _ z => Real.sqrt Q.η * Q.v t z κ) (entryArr (Cc hh (n - 1)) (n - 1) w t v)

/-- The fast term `√η ∑_j G_{κ j} ∂_{z_j} C_{n-1}`. -/
def fluxXB (Q : LiftOperatorData ι (fun _ => ℝ) Dm) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (w : ι) (hh n : ℕ) (t : ℝ) (v : ι) (κ : Fin 2) : CArr :=
  Real.sqrt Q.η • ∑ j : Fin 2, mulArr (fun X _ => Q.G t X κ j)
    (fastArr j (entryArr (Cc hh (n - 1)) (n - 1) w t v))

/-- The slow term `-η ∑_j G_{κ j} ∂_{X_j} C_{n-2}` (for `2 ≤ n`). -/
def fluxXC (Q : LiftOperatorData ι (fun _ => ℝ) Dm) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (w : ι) (hh n : ℕ) (t : ℝ) (v : ι) (κ : Fin 2) : CArr :=
  if 2 ≤ n then -(Q.η • ∑ j : Fin 2, mulArr (fun X _ => Q.G t X κ j)
    (slowArr j (entryArr (Cc hh (n - 2)) (n - 2) w t v))) else 0

/-- The source-flux term `∑_{j=1}^{min Dm n} √η ∂_ε^{j-1}/(j-1)! flux |_{ε=0}` (for `hh ≠ 0`). -/
def fluxXD (Q : LiftOperatorData ι (fun _ => ℝ) Dm) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (w : ι) (hh n : ℕ) (t : ℝ) (v : ι) (κ : Fin 2) : CArr :=
  if hh = 0 then 0 else ∑ j ∈ Finset.Icc 1 (min Dm n), Real.sqrt Q.η •
    fluxG Q.edge (Real.sqrt Q.η) t κ (fun u => entryArr (Cc (hh - 1) (n - j)) (n - j) w t u) v
      (j - 1)

/-- **The coefficient array of the slow flux `liftFluxX`** for the test field `single w a`,
component `v`, direction `κ`. -/
def fluxXArr (Q : LiftOperatorData ι (fun _ => ℝ) Dm) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (w : ι) (hh n : ℕ) (t : ℝ) (v : ι) (κ : Fin 2) : CArr :=
  fluxXA Q Cc w hh n t v κ - fluxXB Q Cc w hh n t v κ + fluxXC Q Cc w hh n t v κ
    - fluxXD Q Cc w hh n t v κ

omit [Fintype ι] in
theorem arrSupp_fluxXA (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) (hh n : ℕ) (t : ℝ) (v : ι) (κ : Fin 2) :
    ArrSupp (n - 1) (fluxXA Q Cc w hh n t v κ) :=
  arrSupp_mulArr _ (arrSupp_entryArr _ _ _ _ _)

omit [Fintype ι] in
theorem arrSupp_fluxXB (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) (hh n : ℕ) (t : ℝ) (v : ι) (κ : Fin 2) :
    ArrSupp (n - 1) (fluxXB Q Cc w hh n t v κ) :=
  ArrSupp.smul _ (ArrSupp.sum _ fun j _ =>
    arrSupp_mulArr _ (arrSupp_fastArr j (arrSupp_entryArr _ _ _ _ _)))

omit [Fintype ι] in
theorem arrSupp_fluxXC (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) (hh n : ℕ) (t : ℝ) (v : ι) (κ : Fin 2) :
    ArrSupp (n - 1) (fluxXC Q Cc w hh n t v κ) := by
  unfold fluxXC
  split_ifs with h
  · refine ArrSupp.neg (ArrSupp.smul _ (ArrSupp.sum _ fun j _ => ?_))
    have := arrSupp_slowArr j (arrSupp_entryArr (Cc hh (n - 2)) (n - 2) w t v)
    exact (arrSupp_mulArr _ this).mono (by omega)
  · exact ArrSupp.zero _

theorem arrSupp_fluxXD (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) (hh n : ℕ) (t : ℝ) (v : ι) (κ : Fin 2) :
    ArrSupp (n - 1) (fluxXD Q Cc w hh n t v κ) := by
  unfold fluxXD
  split_ifs
  · exact ArrSupp.zero _
  · refine ArrSupp.sum _ fun j hj => ArrSupp.smul _ ?_
    have hj' := Finset.mem_Icc.mp hj
    have := (fluxG_gSupp Q.edge (Real.sqrt Q.η) t κ
      (A := fun u => entryArr (Cc (hh - 1) (n - j)) (n - j) w t u)
      (fun u => arrSupp_entryArr _ _ _ _ _) v).1 (j - 1)
    exact this.mono (by omega)

/-- The array vanishes above order `n - 1` (hence above `n`). -/
theorem arrSupp_fluxXArr (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) (hh n : ℕ) (t : ℝ) (v : ι) (κ : Fin 2) :
    ArrSupp (n - 1) (fluxXArr Q Cc w hh n t v κ) :=
  ArrSupp.sub (ArrSupp.add (ArrSupp.sub (arrSupp_fluxXA Q Cc w hh n t v κ)
    (arrSupp_fluxXB Q Cc w hh n t v κ)) (arrSupp_fluxXC Q Cc w hh n t v κ))
    (arrSupp_fluxXD Q Cc w hh n t v κ)

/-- Smoothness: all coefficients are `C^r` in `(X,z)` under the regularity bundle of order
`r + Dm + 2`. -/
theorem arrSmooth_fluxXArr (Q : LiftOperatorData ι (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (w : ι) {hh n : ℕ} {t : ℝ} {r : ℕ}
    (hreg : LiftRegular Q Cc w t hh n (r + Dm + 2)) (v : ι) (κ : Fin 2) :
    ArrSmooth r (fluxXArr Q Cc w hh n t v κ) := by
  have hent : ∀ hh' k, hh' ≤ hh → k ≤ n → ∀ u,
      ArrSmooth (r + Dm + 2) (entryArr (Cc hh' k) k w t u) := fun hh' k h1 h2 u =>
    arrSmooth_entryArr _ _ _ _ _ (hreg.coeff hh' h1 k h2 · · u)
  have hG : ∀ i j, ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => Q.G t p.1 i j) :=
    fun i j => (hreg.metric i j).of_le (by exact_mod_cast (by omega : r + 1 ≤ r + Dm + 2))
  have hG' : ∀ i j, ContDiff ℝ (r : WithTop ℕ∞) (fun p : Vec 2 × Vec 2 => Q.G t p.1 i j) :=
    fun i j => (hG i j).of_le (by exact_mod_cast Nat.le_succ r)
  have hB1 : ArrSmooth (r + 1) (entryArr (Cc hh (n - 1)) (n - 1) w t v) :=
    (hent hh (n - 1) le_rfl (by omega) v).mono (by omega)
  unfold fluxXArr
  refine ArrSmooth.sub (ArrSmooth.add (ArrSmooth.sub ?_ ?_) ?_) ?_
  · exact arrSmooth_mulArr (contDiff_const.mul
      ((hreg.drift κ).of_le (by exact_mod_cast (by omega : r ≤ r + Dm + 2))))
      (hB1.mono (by omega))
  · exact ArrSmooth.smul _ (ArrSmooth.sum _ fun j _ =>
      arrSmooth_mulArr (hG' κ j) (arrSmooth_fastArr j hB1))
  · unfold fluxXC
    split_ifs with h2
    · exact (arrSmoothSub r).neg_mem (ArrSmooth.smul _ (ArrSmooth.sum _ fun j _ =>
        arrSmooth_mulArr (hG' κ j)
          (arrSmooth_slowArr j ((hent hh (n - 2) le_rfl (by omega) v).mono (by omega)))))
    · exact ArrSmooth.zero _
  · unfold fluxXD
    split_ifs with h0
    · exact ArrSmooth.zero _
    · refine ArrSmooth.sum _ fun j hj => ArrSmooth.smul _ ?_
      have hj' := Finset.mem_Icc.mp hj
      exact fluxG_gSmooth Q.edge _ t κ (r := r)
        (fun u => (hent (hh - 1) (n - j) (by omega) (by omega) u).mono (by omega))
        (fun v u d γ hγ α => (hreg.edge v u d γ hγ α κ).of_le
          (by exact_mod_cast (by omega : r ≤ r + Dm + 2))) v (j - 1)
end

end AVRegularity.Providers.GenSem
end
