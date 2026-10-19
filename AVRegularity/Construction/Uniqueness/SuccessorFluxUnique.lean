-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Uniqueness.CellFieldUnique
public import AVRegularity.Definitions.Construction.Preparation

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.Uniqueness

/-! Uniqueness of the lift sequence on a window, from the window uniqueness of the cell inverse.

The lift relation determines `C_n^{(hh)}` by recursion on `(hh, n)` in the lexicographic order:
the cell source of `C_n^{(hh)}` involves only `C_{n'}^{(hh')}` with `(hh', n') < (hh, n)`, the cell
inverse is unique, and symmetric word arrays are determined by their action on test fields. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The coefficient arrays of grade `hh` and degree `n` agree on the window. -/
def CoeffEq (Cc Cc' : ℕ → ℕ → LiftCoeff ι h) (t₀ t₁ : ℝ) (hh n : ℕ) : Prop :=
  ∀ t ∈ Icc t₀ t₁, ∀ m (α : DerivativeWord2 m), Cc hh n m α t = Cc' hh n m α t

theorem liftApply_congr {n : ℕ} {B B' : LiftCoeff ι h} {a a' : ℝ → Vec 2 → ∀ i, h i} {t : ℝ}
    (hB : ∀ m ≤ n, ∀ α : DerivativeWord2 m, B m α t = B' m α t) (ha : a t = a' t) :
    liftApply n B a t = liftApply n B' a' t := by
  funext X z v
  unfold liftApply
  refine Finset.sum_congr rfl (fun m hm => ?_)
  refine Finset.sum_congr rfl (fun α _ => ?_)
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [hB m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) α, ha]

theorem liftApply_congr_of {Cc Cc' : ℕ → ℕ → LiftCoeff ι h} {t₀ t₁ : ℝ} {hh k : ℕ}
    (hP : CoeffEq Cc Cc' t₀ t₁ hh k) {t : ℝ} (ht : t ∈ Icc t₀ t₁)
    {a a' : ℝ → Vec 2 → ∀ i, h i} (ha : a t = a' t) :
    liftApply k (Cc hh k) a t = liftApply k (Cc' hh k) a' t :=
  liftApply_congr (fun m _ α => hP t ht m α) ha

theorem liftA_congr {Dm : ℕ} (Q : LiftOperatorData ι h Dm) {Cc Cc' : ℕ → ℕ → LiftCoeff ι h}
    {t₀ t₁ : ℝ} (hh n : ℕ) {t : ℝ} (ht : t ∈ Icc t₀ t₁) (a : ℝ → Vec 2 → ∀ i, h i)
    (h1 : CoeffEq Cc Cc' t₀ t₁ hh (n - 1)) (h2 : 2 ≤ n → CoeffEq Cc Cc' t₀ t₁ hh (n - 2))
    (h3 : 0 < hh → ∀ k, CoeffEq Cc Cc' t₀ t₁ (hh - 1) k) :
    liftA Q Cc a hh n t = liftA Q Cc' a hh n t := by
  funext X z
  unfold liftA
  have e1 := liftApply_congr_of h1 ht (a := a) (a' := a) rfl
  rw [e1]
  by_cases hn2 : 2 ≤ n
  · have e2 := liftApply_congr_of (h2 hn2) ht (a := a) (a' := a) rfl
    simp only [hn2, ↓reduceIte, e2]
    by_cases hh0 : hh = 0
    · simp [hh0]
    · have e3 : ∀ j, liftApply (n - j) (Cc (hh - 1) (n - j)) a t =
          liftApply (n - j) (Cc' (hh - 1) (n - j)) a t :=
        fun j => liftApply_congr_of (h3 (Nat.pos_of_ne_zero hh0) (n - j)) ht (a := a) (a' := a) rfl
      simp only [hh0, ↓reduceIte, e3]
  · simp only [hn2, ↓reduceIte]
    by_cases hh0 : hh = 0
    · simp [hh0]
    · have e3 : ∀ j, liftApply (n - j) (Cc (hh - 1) (n - j)) a t =
          liftApply (n - j) (Cc' (hh - 1) (n - j)) a t :=
        fun j => liftApply_congr_of (h3 (Nat.pos_of_ne_zero hh0) (n - j)) ht (a := a) (a' := a) rfl
      simp only [hh0, ↓reduceIte, e3]

theorem liftMean_congr {Dm : ℕ} (Q : LiftOperatorData ι h Dm) {Cc Cc' : ℕ → ℕ → LiftCoeff ι h}
    {t₀ t₁ : ℝ} (hh n : ℕ) {t : ℝ} (ht : t ∈ Icc t₀ t₁) (a : ℝ → Vec 2 → ∀ i, h i)
    (h1 : CoeffEq Cc Cc' t₀ t₁ hh (n - 1)) (h2 : 2 ≤ n → CoeffEq Cc Cc' t₀ t₁ hh (n - 2))
    (h3 : 0 < hh → ∀ k, CoeffEq Cc Cc' t₀ t₁ (hh - 1) k) :
    liftMean Q Cc a hh n t = liftMean Q Cc' a hh n t := by
  funext X
  unfold liftMean
  rw [liftA_congr Q hh n ht a h1 h2 h3]


theorem liftCellSource_congr {Dm : ℕ} (Q : LiftOperatorData ι h Dm)
    {Cc Cc' : ℕ → ℕ → LiftCoeff ι h} {t₀ t₁ : ℝ} (hh n : ℕ) (hn : 1 ≤ n)
    (IH : ∀ hh' n', (hh' < hh ∨ (hh' = hh ∧ n' < n)) → CoeffEq Cc Cc' t₀ t₁ hh' n')
    {t : ℝ} (ht : t ∈ Icc t₀ t₁) (a : ℝ → Vec 2 → ∀ i, h i) :
    liftCellSource Q Cc a hh n t = liftCellSource Q Cc' a hh n t := by
  funext X z
  unfold liftCellSource
  have hA := liftA_congr Q (Cc := Cc) (Cc' := Cc') hh n ht a
    (IH hh (n - 1) (Or.inr ⟨rfl, by omega⟩))
    (fun h2 => IH hh (n - 2) (Or.inr ⟨rfl, by omega⟩))
    (fun h0 k => IH (hh - 1) k (Or.inl (by omega)))
  have hM := liftMean_congr Q (Cc := Cc) (Cc' := Cc') hh n ht a
    (IH hh (n - 1) (Or.inr ⟨rfl, by omega⟩))
    (fun h2 => IH hh (n - 2) (Or.inr ⟨rfl, by omega⟩))
    (fun h0 k => IH (hh - 1) k (Or.inl (by omega)))
  rw [hA, hM]
  congr 1
  refine Finset.sum_congr rfl (fun j hj => ?_)
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hj' := Finset.mem_Icc.mp hj
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hmean : liftMean Q Cc a p.2 (n - j) t = liftMean Q Cc' a p.2 (n - j) t :=
    liftMean_congr Q (Cc := Cc) (Cc' := Cc') p.2 (n - j) ht a
      (IH p.2 (n - j - 1) (by omega))
      (fun h2 => IH p.2 (n - j - 2) (by omega))
      (fun h0 k => IH (p.2 - 1) k (Or.inl (by omega)))
  have := congrFun (congrFun (liftApply_congr (n := j) (B := Cc p.1 j) (B' := Cc' p.1 j)
    (a := liftMean Q Cc a p.2 (n - j)) (a' := liftMean Q Cc' a p.2 (n - j)) (t := t)
    (fun m _ α => IH p.1 j (by omega) t ht m α) hmean) X) z
  exact congrArg (fun w => w) this

/-- Uniqueness of the lift sequence on the window, from window bounds of the metric and drift. -/
theorem lift_sequence_unique_window [∀ i, FiniteDimensional ℝ (h i)] {Dm : ℕ}
    (Q : LiftOperatorData ι h Dm) (t₀ t₁ : ℝ) (hab : t₀ ≤ t₁)
    (hW : ∀ X, ∃ lo A Mv : ℝ, WindowData (fun t => Matrix.of (Q.G t X)) Q.v t₀ t₁ lo A Mv)
    (sX sZ N H : ℕ) (Cc Cc' : ℕ → ℕ → LiftCoeff ι h)
    (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (hC' : IsLiftSequence Q sX sZ t₀ t₁ N H Cc') :
    ∀ hh ≤ H, ∀ n m (α : DerivativeWord2 m), ∀ t ∈ Set.Icc t₀ t₁, ∀ X z v u,
      Cc hh n m α t X z v u = Cc' hh n m α t X z v u := by
  classical
  have main : ∀ hh ≤ H, ∀ n, CoeffEq Cc Cc' t₀ t₁ hh n := by
    intro hh
    induction hh using Nat.strong_induction_on with
    | _ hh ihh =>
    intro hhH n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
    have IH : ∀ hh' n', (hh' < hh ∨ (hh' = hh ∧ n' < n)) → CoeffEq Cc Cc' t₀ t₁ hh' n' := by
      intro hh' n' hlt
      rcases hlt with hlt | ⟨rfl, hn⟩
      · exact ihh hh' hlt (by omega) n'
      · exact ihn n' hn
    -- the coefficient determination
    have det : ∀ t ∈ Icc t₀ t₁, ∀ X z, (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
        liftApply n (Cc hh n) (fun _ => a₀) t X z = liftApply n (Cc' hh n) (fun _ => a₀) t X z) →
        ∀ m (α : DerivativeWord2 m), ∀ v u, Cc hh n m α t X z v u = Cc' hh n m α t X z v u := by
      intro t ht X z hap m α v u
      by_cases hmn : m ≤ n
      · exact coeff_eq_of_apply_eq n (Cc hh n) (Cc' hh n)
          (fun m α σ => (hC.2.2.2.2.1 hh hhH n m α σ))
          (fun m α σ => (hC'.2.2.2.2.1 hh hhH n m α σ)) t X z hap m hmn α v u
      · have hmn' := not_le.mp hmn
        rw [hC.2.2.2.1 hh hhH n m hmn' α t X z v u, hC'.2.2.2.1 hh hhH n m hmn' α t X z v u]
    intro t ht m α
    funext X z v u
    by_cases hn0 : n = 0
    · subst hn0
      by_cases hh0 : hh = 0
      · subst hh0
        refine det t ht X z (fun a₀ ha₀ => ?_) m α v u
        rw [hC.1 a₀ ha₀ t ht X z, hC'.1 a₀ ha₀ t ht X z]
      · rw [hC.2.1 hh (by omega) hhH m α t X z v u, hC'.2.1 hh (by omega) hhH m α t X z v u]
    · by_cases hnN : N < n
      · rw [hC.2.2.1 hh hhH n hnN m α t X z v u, hC'.2.2.1 hh hhH n hnN m α t X z v u]
      · have hnN' := not_lt.mp hnN
        refine det t ht X z (fun a₀ ha₀ => ?_) m α v u
        obtain ⟨lo, A, Mv, hWX⟩ := hW X
        have hcX := hC.2.2.2.2.2.2 hh hhH n (by omega) hnN' a₀ ha₀ X
        have hcX' := hC'.2.2.2.2.2.2 hh hhH n (by omega) hnN' a₀ ha₀ X
        have hsrc : ∀ t ∈ Icc t₀ t₁, ∀ z, liftCellSource Q Cc (fun _ => a₀) hh n t X z =
            liftCellSource Q Cc' (fun _ => a₀) hh n t X z := fun t ht z =>
          congrFun (congrFun (liftCellSource_congr Q (Cc := Cc) (Cc' := Cc') hh n (by omega) IH ht
            (fun _ => a₀)) X) z
        exact cellField_unique_window hab hWX (g := fun t z => liftCellSource Q Cc (fun _ => a₀) hh n t X z)
          (g' := fun t z => liftCellSource Q Cc' (fun _ => a₀) hh n t X z)
          (fun t ht z => hsrc t ht z) hcX hcX' t ht z
  intro hh hhH n m α t ht X z v u
  exact congrFun (congrFun (congrFun (congrFun (main hh hhH n t ht m α) X) z) v) u

end AVRegularity.Uniqueness
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Uniqueness

/-! Window data of the cell equation from a symmetric, positive definite, bounded metric and a
bounded drift. -/

/-- The entries of a symmetric matrix with quadratic form between `lo` and `hi` are bounded. -/
theorem entry_bound_of_quadratic (G : Matrix (Fin 2) (Fin 2) ℝ) (hs : G 0 1 = G 1 0)
    (lo hi : ℝ) (hlo : 0 < lo)
    (hq : ∀ ξ : Fin 2 → ℝ, lo * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G i j * ξ i * ξ j ∧
      ∑ i, ∑ j, G i j * ξ i * ξ j ≤ hi * ∑ i, ξ i ^ 2) :
    ∀ i j, |G i j| ≤ hi := by
  have h0 := hq ![1, 0]
  have h1 := hq ![0, 1]
  have hp := hq ![1, 1]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 hp
  norm_num at h0 h1 hp
  have hlo' : lo ≤ hi := by linarith [h0.1, h0.2]
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, abs_le] <;>
    constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2, hp.1, hp.2, hs]

/-- Window data from the elliptic hypotheses of the operator-only uniqueness. -/
theorem windowData_of_elliptic (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (t₀ t₁ lo hi Mv : ℝ) (hsymm : ∀ t, G t 0 1 = G t 1 0) (hlo : 0 < lo)
    (hq : ∀ t ∈ Set.Icc t₀ t₁, ∀ ξ : Fin 2 → ℝ,
      lo * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t i j * ξ i * ξ j ∧
        ∑ i, ∑ j, G t i j * ξ i * ξ j ≤ hi * ∑ i, ξ i ^ 2)
    (hv : ∀ t ∈ Set.Icc t₀ t₁, ∀ z, ‖v t z‖ ≤ Mv) :
    WindowData G v t₀ t₁ lo hi Mv where
  lo_pos := hlo
  coer := fun t ht ξ => (hq t ht ξ).1
  ent := fun t ht => entry_bound_of_quadratic (G t) (hsymm t) lo hi hlo (hq t ht)
  vb := fun t ht z k => (by
    have := norm_le_pi_norm (v t z) k
    rw [Real.norm_eq_abs] at this
    exact this.trans (hv t ht z))

end AVRegularity.Uniqueness
end
end

section
/-! Uniqueness of the localized lift sequence (`IsLiftSequenceOn Ω`) on a window,
for an open set `Ω` of slow offsets.

The cell source of `C_n^{(hh)}` at a slow offset `X` reads the lower coefficients only through
their germs at `X` (values, fast derivatives, and slow derivatives). On an open `Ω` the germs at
`X ∈ Ω` are determined by the values on `Ω` (`LocEq`), so the recursion of the lift sequence
runs on `Ω`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution Filter
  Topology

namespace AVRegularity.Uniqueness

/-! ### Agreement on an open set of slow offsets -/

section LocEq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set (Vec 2)}

/-- Two fields agree for the slow offsets of `Ω`. -/
def LocEq (Ω : Set (Vec 2)) (Φ Φ' : Vec 2 → Vec 2 → E) : Prop := ∀ X ∈ Ω, ∀ z, Φ X z = Φ' X z

theorem LocEq.slowPartial (hΩ : IsOpen Ω) {Φ Φ' : Vec 2 → Vec 2 → E} (h : LocEq Ω Φ Φ')
    (i : Fin 2) : LocEq Ω (AVRegularity.slowPartial i Φ) (AVRegularity.slowPartial i Φ') := by
  intro X hX z
  unfold AVRegularity.slowPartial
  have hev : (fun X' => Φ X' z) =ᶠ[𝓝 X] fun X' => Φ' X' z := by
    filter_upwards [hΩ.mem_nhds hX] with X' hX' using h X' hX' z
  rw [hev.fderiv_eq]

theorem LocEq.fastPartial {Φ Φ' : Vec 2 → Vec 2 → E} (h : LocEq Ω Φ Φ') (i : Fin 2) :
    LocEq Ω (AVRegularity.fastPartial i Φ) (AVRegularity.fastPartial i Φ') := by
  intro X hX z
  unfold AVRegularity.fastPartial
  rw [show (fun z' => Φ X z') = fun z' => Φ' X z' from funext (h X hX)]

theorem LocEq.dEps (hΩ : IsOpen Ω) {Φ Φ' : Vec 2 → Vec 2 → E} (h : LocEq Ω Φ Φ') (η ε : ℝ)
    (i : Fin 2) : LocEq Ω (AVRegularity.dEps η ε i Φ) (AVRegularity.dEps η ε i Φ') := by
  intro X hX z
  unfold AVRegularity.dEps
  rw [h.fastPartial i X hX z, h.slowPartial hΩ i X hX z]

theorem LocEq.foldl_dEps (hΩ : IsOpen Ω) (η ε : ℝ) :
    ∀ (l : List (Fin 2)) {Φ Φ' : Vec 2 → Vec 2 → E}, LocEq Ω Φ Φ' →
      LocEq Ω (l.foldl (fun Ψ i => AVRegularity.dEps η ε i Ψ) Φ) (l.foldl (fun Ψ i => AVRegularity.dEps η ε i Ψ) Φ')
  | [], _, _, h => h
  | i :: l, _, _, h => LocEq.foldl_dEps hΩ η ε l (h.dEps hΩ η ε i)

theorem LocEq.dEpsWord (hΩ : IsOpen Ω) {Φ Φ' : Vec 2 → Vec 2 → E} (h : LocEq Ω Φ Φ')
    (η ε : ℝ) {m : ℕ} (α : DerivativeWord2 m) :
    LocEq Ω (AVRegularity.dEpsWord η ε α Φ) (AVRegularity.dEpsWord η ε α Φ') :=
  LocEq.foldl_dEps hΩ η ε _ h

/-- Ordered derivatives of functions agreeing on an open set agree there. -/
theorem eqOn_orderedDerivative (hΩ : IsOpen Ω) :
    ∀ (l : List (Fin 2)) {f f' : Vec 2 → E}, EqOn f f' Ω →
      EqOn (l.foldl (fun g i => fun x => fderiv ℝ g x (basisVec i)) f)
        (l.foldl (fun g i => fun x => fderiv ℝ g x (basisVec i)) f') Ω
  | [], _, _, h => h
  | i :: l, f, f', h => by
      refine eqOn_orderedDerivative hΩ l (f := fun x => fderiv ℝ f x (basisVec i))
        (f' := fun x => fderiv ℝ f' x (basisVec i)) fun x hx => ?_
      have hev : f =ᶠ[𝓝 x] f' := by
        filter_upwards [hΩ.mem_nhds hx] with y hy using h hy
      simp only [hev.fderiv_eq]

end LocEq

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {Ω : Set (Vec 2)}

theorem LocEq.sourceFlux (hΩ : IsOpen Ω) {Dm : ℕ} (edge : ConstituentEdges Dm h) (η ε t : ℝ)
    {Φ Φ' : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : LocEq Ω Φ Φ') (k : Fin 2) :
    LocEq Ω (AVRegularity.sourceFlux edge η ε t Φ k) (AVRegularity.sourceFlux edge η ε t Φ' k) := by
  intro X hX z
  have hW : ∀ {m : ℕ} (α : DerivativeWord2 m),
      AVRegularity.dEpsWord η ε α Φ X z = AVRegularity.dEpsWord η ε α Φ' X z := fun α => hΦ.dEpsWord hΩ η ε α X hX z
  unfold AVRegularity.sourceFlux
  simp only [hW]

theorem LocEq.sourceOp (hΩ : IsOpen Ω) {Dm : ℕ} (edge : ConstituentEdges Dm h) (η ε t : ℝ)
    {Φ Φ' : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : LocEq Ω Φ Φ') :
    LocEq Ω (AVRegularity.sourceOp edge η ε t Φ) (AVRegularity.sourceOp edge η ε t Φ') := by
  intro X hX z
  unfold AVRegularity.sourceOp
  refine Finset.sum_congr rfl fun k _ => ?_
  exact ((hΦ.sourceFlux hΩ edge η ε t k).dEps hΩ η ε k) X hX z

theorem LocEq.sourceCoeff (hΩ : IsOpen Ω) {Dm : ℕ} (edge : ConstituentEdges Dm h) (η : ℝ)
    (j : ℕ) (t : ℝ) {Φ Φ' : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : LocEq Ω Φ Φ') :
    LocEq Ω (AVRegularity.sourceCoeff edge η j t Φ) (AVRegularity.sourceCoeff edge η j t Φ') := by
  intro X hX z
  unfold AVRegularity.sourceCoeff
  rw [show (fun ε : ℝ => AVRegularity.sourceOp edge η ε t Φ X z) = fun ε => AVRegularity.sourceOp edge η ε t Φ' X z from
    funext fun ε => hΦ.sourceOp hΩ edge η ε t X hX z]

theorem LocEq.cellB1 (hΩ : IsOpen Ω) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    {Φ Φ' : Vec 2 → Vec 2 → E} (hΦ : LocEq Ω Φ Φ') :
    LocEq Ω (AVRegularity.cellB1 η G v t Φ) (AVRegularity.cellB1 η G v t Φ') := by
  intro X hX z
  have hG : ∀ i j, LocEq Ω (fun X' z' => G t X' i j • AVRegularity.fastPartial j Φ X' z')
      (fun X' z' => G t X' i j • AVRegularity.fastPartial j Φ' X' z') := fun i j X' hX' z' => by
    beta_reduce
    rw [hΦ.fastPartial j X' hX' z']
  unfold AVRegularity.cellB1
  simp only [hΦ.slowPartial hΩ _ X hX z, (hΦ.slowPartial hΩ _).fastPartial _ X hX z,
    (hG _ _).slowPartial hΩ _ X hX z]

theorem LocEq.cellB2 (hΩ : IsOpen Ω) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ) {Φ Φ' : Vec 2 → Vec 2 → E}
    (hΦ : LocEq Ω Φ Φ') : LocEq Ω (AVRegularity.cellB2 η G t Φ) (AVRegularity.cellB2 η G t Φ') := by
  intro X hX z
  have hG : ∀ i j, LocEq Ω (fun X' z' => G t X' i j • AVRegularity.slowPartial j Φ X' z')
      (fun X' z' => G t X' i j • AVRegularity.slowPartial j Φ' X' z') := fun i j X' hX' z' => by
    beta_reduce
    rw [hΦ.slowPartial hΩ j X' hX' z']
  unfold AVRegularity.cellB2
  simp only [(hG _ _).slowPartial hΩ _ X hX z]

/-! ### The lift operators on an open set -/

/-- The coefficient arrays of grade `hh` and degree `n` agree on the window and on `Ω`. -/
def CoeffEqOn (Ω : Set (Vec 2)) (Cc Cc' : ℕ → ℕ → LiftCoeff ι h) (t₀ t₁ : ℝ) (hh n : ℕ) : Prop :=
  ∀ t ∈ Icc t₀ t₁, ∀ m (α : DerivativeWord2 m), ∀ X ∈ Ω, Cc hh n m α t X = Cc' hh n m α t X

theorem liftApply_locEq {n : ℕ} {B B' : LiftCoeff ι h} {a a' : ℝ → Vec 2 → ∀ i, h i} {t : ℝ}
    (hΩ : IsOpen Ω) (hB : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ X ∈ Ω, B m α t X = B' m α t X)
    (ha : EqOn (a t) (a' t) Ω) :
    LocEq Ω (liftApply n B a t) (liftApply n B' a' t) := by
  intro X hX z
  funext v
  unfold liftApply
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun u _ => ?_
  rw [hB m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) α X hX,
    show orderedDerivative α (a t) X = orderedDerivative α (a' t) X from
      eqOn_orderedDerivative hΩ (List.ofFn α) ha hX]

theorem liftApply_locEq_of {Cc Cc' : ℕ → ℕ → LiftCoeff ι h} {t₀ t₁ : ℝ} {hh k : ℕ}
    (hΩ : IsOpen Ω) (hP : CoeffEqOn Ω Cc Cc' t₀ t₁ hh k) {t : ℝ} (ht : t ∈ Icc t₀ t₁)
    {a a' : ℝ → Vec 2 → ∀ i, h i} (ha : EqOn (a t) (a' t) Ω) :
    LocEq Ω (liftApply k (Cc hh k) a t) (liftApply k (Cc' hh k) a' t) :=
  liftApply_locEq hΩ (fun m _ α X hX => hP t ht m α X hX) ha

theorem liftA_locEq {Dm : ℕ} (Q : LiftOperatorData ι h Dm) {Cc Cc' : ℕ → ℕ → LiftCoeff ι h}
    {t₀ t₁ : ℝ} (hΩ : IsOpen Ω) (hh n : ℕ) {t : ℝ} (ht : t ∈ Icc t₀ t₁)
    (a : ℝ → Vec 2 → ∀ i, h i)
    (h1 : CoeffEqOn Ω Cc Cc' t₀ t₁ hh (n - 1)) (h2 : 2 ≤ n → CoeffEqOn Ω Cc Cc' t₀ t₁ hh (n - 2))
    (h3 : 0 < hh → ∀ k, CoeffEqOn Ω Cc Cc' t₀ t₁ (hh - 1) k) :
    LocEq Ω (liftA Q Cc a hh n t) (liftA Q Cc' a hh n t) := by
  intro X hX z
  have e1 := (liftApply_locEq_of hΩ h1 ht (a := a) (a' := a) (fun _ _ => rfl)).cellB1 hΩ Q.η Q.G
    Q.v t X hX z
  have e2 : (if 2 ≤ n then AVRegularity.cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) a t) X z
      else 0) = (if 2 ≤ n then AVRegularity.cellB2 Q.η Q.G t
        (liftApply (n - 2) (Cc' hh (n - 2)) a t) X z else 0) := by
    by_cases hn2 : 2 ≤ n
    · simp only [hn2, ↓reduceIte]
      exact (liftApply_locEq_of hΩ (h2 hn2) ht (a := a) (a' := a) (fun _ _ => rfl)).cellB2 hΩ Q.η
        Q.G t X hX z
    · simp only [hn2, ↓reduceIte]
  have e3 : (if hh = 0 then 0 else ∑ j ∈ Finset.range (min Dm n + 1),
      AVRegularity.sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) a t) X z) =
      (if hh = 0 then 0 else ∑ j ∈ Finset.range (min Dm n + 1),
      AVRegularity.sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc' (hh - 1) (n - j)) a t) X z) := by
    by_cases hh0 : hh = 0
    · simp only [hh0, ↓reduceIte]
    · simp only [hh0, ↓reduceIte]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (liftApply_locEq_of hΩ (h3 (Nat.pos_of_ne_zero hh0) (n - j)) ht (a := a) (a' := a)
        (fun _ _ => rfl)).sourceCoeff hΩ Q.edge Q.η j t X hX z
  show liftA Q Cc a hh n t X z = liftA Q Cc' a hh n t X z
  unfold liftA
  rw [e1, e2, e3]

theorem liftMean_eqOn {Dm : ℕ} (Q : LiftOperatorData ι h Dm) {Cc Cc' : ℕ → ℕ → LiftCoeff ι h}
    {t₀ t₁ : ℝ} (hΩ : IsOpen Ω) (hh n : ℕ) {t : ℝ} (ht : t ∈ Icc t₀ t₁)
    (a : ℝ → Vec 2 → ∀ i, h i)
    (h1 : CoeffEqOn Ω Cc Cc' t₀ t₁ hh (n - 1)) (h2 : 2 ≤ n → CoeffEqOn Ω Cc Cc' t₀ t₁ hh (n - 2))
    (h3 : 0 < hh → ∀ k, CoeffEqOn Ω Cc Cc' t₀ t₁ (hh - 1) k) :
    EqOn (liftMean Q Cc a hh n t) (liftMean Q Cc' a hh n t) Ω := by
  intro X hX
  unfold liftMean
  rw [show (fun z => liftA Q Cc a hh n t X z) = fun z => liftA Q Cc' a hh n t X z from
    funext (liftA_locEq Q hΩ hh n ht a h1 h2 h3 X hX)]

theorem liftCellSource_locEq {Dm : ℕ} (Q : LiftOperatorData ι h Dm)
    {Cc Cc' : ℕ → ℕ → LiftCoeff ι h} {t₀ t₁ : ℝ} (hΩ : IsOpen Ω) (hh n : ℕ) (hn : 1 ≤ n)
    (IH : ∀ hh' n', (hh' < hh ∨ (hh' = hh ∧ n' < n)) → CoeffEqOn Ω Cc Cc' t₀ t₁ hh' n')
    {t : ℝ} (ht : t ∈ Icc t₀ t₁) (a : ℝ → Vec 2 → ∀ i, h i) :
    LocEq Ω (liftCellSource Q Cc a hh n t) (liftCellSource Q Cc' a hh n t) := by
  intro X hX z
  unfold liftCellSource
  have hA := liftA_locEq Q (Cc := Cc) (Cc' := Cc') hΩ hh n ht a
    (IH hh (n - 1) (Or.inr ⟨rfl, by omega⟩))
    (fun h2 => IH hh (n - 2) (Or.inr ⟨rfl, by omega⟩))
    (fun h0 k => IH (hh - 1) k (Or.inl (by omega))) X hX z
  have hM := liftMean_eqOn Q (Cc := Cc) (Cc' := Cc') hΩ hh n ht a
    (IH hh (n - 1) (Or.inr ⟨rfl, by omega⟩))
    (fun h2 => IH hh (n - 2) (Or.inr ⟨rfl, by omega⟩))
    (fun h0 k => IH (hh - 1) k (Or.inl (by omega))) hX
  have hsum : ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean Q Cc a p.2 (n - j)) t X z =
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc' p.1 j) (liftMean Q Cc' a p.2 (n - j)) t X z := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hmean : EqOn (liftMean Q Cc a p.2 (n - j) t) (liftMean Q Cc' a p.2 (n - j) t) Ω :=
      liftMean_eqOn Q (Cc := Cc) (Cc' := Cc') hΩ p.2 (n - j) ht a
        (IH p.2 (n - j - 1) (by omega))
        (fun h2 => IH p.2 (n - j - 2) (by omega))
        (fun h0 k => IH (p.2 - 1) k (Or.inl (by omega)))
    exact liftApply_locEq (n := j) (B := Cc p.1 j) (B' := Cc' p.1 j)
      (a := liftMean Q Cc a p.2 (n - j)) (a' := liftMean Q Cc' a p.2 (n - j)) (t := t) hΩ
      (fun m _ α X' hX' => IH p.1 j (by omega) t ht m α X' hX') hmean X hX z
  rw [hA, hM, hsum]

/-! ### Uniqueness on an open set -/

/-- **Uniqueness of the localized lift sequence on the window**, from window bounds of the metric
and the drift at the slow offsets of the open set `Ω`. -/
theorem lift_sequence_unique_window_on [∀ i, FiniteDimensional ℝ (h i)] {Dm : ℕ}
    (Q : LiftOperatorData ι h Dm) (t₀ t₁ : ℝ) (hab : t₀ ≤ t₁) (hΩ : IsOpen Ω)
    (hW : ∀ X ∈ Ω, ∃ lo A Mv : ℝ, WindowData (fun t => Matrix.of (Q.G t X)) Q.v t₀ t₁ lo A Mv)
    (sX sZ N H : ℕ) (Cc Cc' : ℕ → ℕ → LiftCoeff ι h)
    (hC : IsLiftSequenceOn Ω Q sX sZ t₀ t₁ N H Cc)
    (hC' : IsLiftSequenceOn Ω Q sX sZ t₀ t₁ N H Cc') :
    ∀ hh ≤ H, ∀ n m (α : DerivativeWord2 m), ∀ t ∈ Set.Icc t₀ t₁, ∀ X ∈ Ω, ∀ z v u,
      Cc hh n m α t X z v u = Cc' hh n m α t X z v u := by
  classical
  have main : ∀ hh ≤ H, ∀ n, CoeffEqOn Ω Cc Cc' t₀ t₁ hh n := by
    intro hh
    induction hh using Nat.strong_induction_on with
    | _ hh ihh =>
    intro hhH n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
    have IH : ∀ hh' n', (hh' < hh ∨ (hh' = hh ∧ n' < n)) → CoeffEqOn Ω Cc Cc' t₀ t₁ hh' n' := by
      intro hh' n' hlt
      rcases hlt with hlt | ⟨rfl, hn⟩
      · exact ihh hh' hlt (by omega) n'
      · exact ihn n' hn
    have det : ∀ t ∈ Icc t₀ t₁, ∀ X z, (∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ →
        liftApply n (Cc hh n) (fun _ => a₀) t X z = liftApply n (Cc' hh n) (fun _ => a₀) t X z) →
        ∀ m (α : DerivativeWord2 m), ∀ v u, Cc hh n m α t X z v u = Cc' hh n m α t X z v u := by
      intro t ht X z hap m α v u
      by_cases hmn : m ≤ n
      · exact coeff_eq_of_apply_eq n (Cc hh n) (Cc' hh n)
          (fun m α σ => (hC.2.2.2.2.1 hh hhH n m α σ))
          (fun m α σ => (hC'.2.2.2.2.1 hh hhH n m α σ)) t X z hap m hmn α v u
      · have hmn' := not_le.mp hmn
        rw [hC.2.2.2.1 hh hhH n m hmn' α t X z v u, hC'.2.2.2.1 hh hhH n m hmn' α t X z v u]
    intro t ht m α X hX
    funext z v u
    by_cases hn0 : n = 0
    · subst hn0
      by_cases hh0 : hh = 0
      · subst hh0
        refine det t ht X z (fun a₀ ha₀ => ?_) m α v u
        rw [hC.1 a₀ ha₀ t ht X z, hC'.1 a₀ ha₀ t ht X z]
      · rw [hC.2.1 hh (by omega) hhH m α t X z v u, hC'.2.1 hh (by omega) hhH m α t X z v u]
    · by_cases hnN : N < n
      · rw [hC.2.2.1 hh hhH n hnN m α t X z v u, hC'.2.2.1 hh hhH n hnN m α t X z v u]
      · have hnN' := not_lt.mp hnN
        refine det t ht X z (fun a₀ ha₀ => ?_) m α v u
        obtain ⟨lo, A, Mv, hWX⟩ := hW X hX
        have hcX := hC.2.2.2.2.2.2 hh hhH n (by omega) hnN' a₀ ha₀ X hX
        have hcX' := hC'.2.2.2.2.2.2 hh hhH n (by omega) hnN' a₀ ha₀ X hX
        have hsrc : ∀ t ∈ Icc t₀ t₁, ∀ z, liftCellSource Q Cc (fun _ => a₀) hh n t X z =
            liftCellSource Q Cc' (fun _ => a₀) hh n t X z := fun t ht z =>
          liftCellSource_locEq Q (Cc := Cc) (Cc' := Cc') hΩ hh n (by omega) IH ht
            (fun _ => a₀) X hX z
        exact cellField_unique_window hab hWX
          (g := fun t z => liftCellSource Q Cc (fun _ => a₀) hh n t X z)
          (g' := fun t z => liftCellSource Q Cc' (fun _ => a₀) hh n t X z)
          (fun t ht z => hsrc t ht z) hcX hcX' t ht z
  intro hh hhH n m α t ht X hX z v u
  exact congrFun (congrFun (congrFun (main hh hhH n t ht m α X hX) z) v) u

/-! ### From the global relation; the elliptic version -/

theorem IsBoxSmooth.toOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {sX sZ : ℕ}
    {f : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth sX sZ f) (Ω : Set (Vec 2)) :
    IsBoxSmoothOn Ω sX sZ f :=
  ⟨fun X _ => hf.1 X, fun b hb z => (hf.2.1 b hb z).contDiffOn,
    fun a b ha hb => (hf.2.2 a b ha hb).continuousOn⟩

/-- **The global lift relation implies the localized one**, on every set `Ω`. -/
theorem IsLiftSequence.toOn [∀ i, FiniteDimensional ℝ (h i)] {Dm : ℕ}
    {Q : LiftOperatorData ι h Dm} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (Ω : Set (Vec 2)) :
    IsLiftSequenceOn Ω Q sX sZ t₀ t₁ N H Cc :=
  ⟨hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1,
    fun hh hhH n m α v u t ht => ⟨IsBoxSmooth.toOn (hC.2.2.2.2.2.1 hh hhH n m α v u t ht).1 Ω,
      (hC.2.2.2.2.2.1 hh hhH n m α v u t ht).2⟩,
    fun hh hhH n hn1 hnN a₀ ha₀ X _ => hC.2.2.2.2.2.2 hh hhH n hn1 hnN a₀ ha₀ X⟩

end AVRegularity.Uniqueness
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Uniqueness

/-! Locality of the lift operators in the lift data.

Two lift operator data `Q`, `Q'` *agree on* an open set `Ω` of slow offsets (`DataAgreeOn`) when
they have the same contrast and drift, their metrics agree on `Ω`, and their source edges have the
same maps and coefficients agreeing on `Ω` (`EdgesAgreeOn`). Then the slow fluxes, the operators
`𝐀_n^{(hh)}`, their means and the cell sources at slow offsets of `Ω` agree, when the coefficients
agree on `Ω` (`liftCellSource_agree`). This lets the representation of the lift coefficients run on
cut-off copies of the data and the lifts, which agree with the true ones near the offsets used. -/

theorem list_sum_map_forall₂ {α β M : Type*} [AddCommMonoid M] {R : α → β → Prop} {f : α → M}
    {g : β → M} : ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      (∀ a b, R a b → f a = g b) → (l.map f).sum = (l'.map g).sum
  | [], [], .nil, _ => rfl
  | a :: _, b :: _, .cons hab hl, hfg => by
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, hfg a b hab,
        list_sum_map_forall₂ hl hfg]

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {Ω : Set (Vec 2)}

/-- Two edge families with the same maps, whose coefficients agree on `Ω`. -/
def EdgesAgreeOn {Dm : ℕ} (Ω : Set (Vec 2)) (e e' : ConstituentEdges Dm h) : Prop :=
  ∀ v u d, List.Forall₂ (fun γ γ' => γ.map = γ'.map ∧
    ∀ α t, ∀ X ∈ Ω, ∀ z, γ.coeff α t X z = γ'.coeff α t X z) (e v u d) (e' v u d)

/-- Two lift operator data agree on `Ω`. -/
structure DataAgreeOn {Dm : ℕ} (Ω : Set (Vec 2)) (Q Q' : LiftOperatorData ι h Dm) : Prop where
  eta : Q.η = Q'.η
  drift : Q.v = Q'.v
  metric : ∀ t, ∀ X ∈ Ω, Q.G t X = Q'.G t X
  edge : EdgesAgreeOn Ω Q.edge Q'.edge

theorem sourceFlux_agree (hΩ : IsOpen Ω) {Dm : ℕ} {e e' : ConstituentEdges Dm h}
    (he : EdgesAgreeOn Ω e e') (η ε t : ℝ) {Φ Φ' : Vec 2 → Vec 2 → ∀ i, h i}
    (hΦ : LocEq Ω Φ Φ') (k : Fin 2) :
    LocEq Ω (AVRegularity.sourceFlux e η ε t Φ k) (AVRegularity.sourceFlux e' η ε t Φ' k) := by
  intro X hX z
  funext v
  unfold AVRegularity.sourceFlux
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun d _ => ?_
  exact list_sum_map_forall₂ (he v u d) fun γ γ' hγ => by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [hγ.2 α t X hX z, hγ.1, hΦ.dEpsWord hΩ η ε α X hX z]

theorem sourceOp_agree (hΩ : IsOpen Ω) {Dm : ℕ} {e e' : ConstituentEdges Dm h}
    (he : EdgesAgreeOn Ω e e') (η ε t : ℝ) {Φ Φ' : Vec 2 → Vec 2 → ∀ i, h i}
    (hΦ : LocEq Ω Φ Φ') :
    LocEq Ω (AVRegularity.sourceOp e η ε t Φ) (AVRegularity.sourceOp e' η ε t Φ') := by
  intro X hX z
  unfold AVRegularity.sourceOp
  refine Finset.sum_congr rfl fun k _ => ?_
  exact ((sourceFlux_agree hΩ he η ε t hΦ k).dEps hΩ η ε k) X hX z

theorem sourceCoeff_agree (hΩ : IsOpen Ω) {Dm : ℕ} {e e' : ConstituentEdges Dm h}
    (he : EdgesAgreeOn Ω e e') (η : ℝ) (j : ℕ) (t : ℝ) {Φ Φ' : Vec 2 → Vec 2 → ∀ i, h i}
    (hΦ : LocEq Ω Φ Φ') :
    LocEq Ω (AVRegularity.sourceCoeff e η j t Φ) (AVRegularity.sourceCoeff e' η j t Φ') := by
  intro X hX z
  unfold AVRegularity.sourceCoeff
  rw [show (fun ε : ℝ => AVRegularity.sourceOp e η ε t Φ X z) =
      fun ε => AVRegularity.sourceOp e' η ε t Φ' X z from
    funext fun ε => sourceOp_agree hΩ he η ε t hΦ X hX z]

theorem cellB1_agree (hΩ : IsOpen Ω) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ) {G G' : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} (hG : ∀ t, ∀ X ∈ Ω, G t X = G' t X)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) {Φ Φ' : Vec 2 → Vec 2 → E} (hΦ : LocEq Ω Φ Φ') :
    LocEq Ω (AVRegularity.cellB1 η G v t Φ) (AVRegularity.cellB1 η G' v t Φ') := by
  intro X hX z
  have hGG : ∀ i j, LocEq Ω (fun X' z' => G t X' i j • AVRegularity.fastPartial j Φ X' z')
      (fun X' z' => G' t X' i j • AVRegularity.fastPartial j Φ' X' z') := fun i j X' hX' z' => by
    beta_reduce
    rw [hΦ.fastPartial j X' hX' z', hG t X' hX']
  unfold AVRegularity.cellB1
  simp only [hΦ.slowPartial hΩ _ X hX z, (hΦ.slowPartial hΩ _).fastPartial _ X hX z,
    (hGG _ _).slowPartial hΩ _ X hX z, hG t X hX]

theorem cellB2_agree (hΩ : IsOpen Ω) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (η : ℝ) {G G' : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} (hG : ∀ t, ∀ X ∈ Ω, G t X = G' t X)
    (t : ℝ) {Φ Φ' : Vec 2 → Vec 2 → E} (hΦ : LocEq Ω Φ Φ') :
    LocEq Ω (AVRegularity.cellB2 η G t Φ) (AVRegularity.cellB2 η G' t Φ') := by
  intro X hX z
  have hGG : ∀ i j, LocEq Ω (fun X' z' => G t X' i j • AVRegularity.slowPartial j Φ X' z')
      (fun X' z' => G' t X' i j • AVRegularity.slowPartial j Φ' X' z') := fun i j X' hX' z' => by
    beta_reduce
    rw [hΦ.slowPartial hΩ j X' hX' z', hG t X' hX']
  unfold AVRegularity.cellB2
  simp only [(hGG _ _).slowPartial hΩ _ X hX z]

theorem liftA_agree {Dm : ℕ} {Q Q' : LiftOperatorData ι h Dm} (hQ : DataAgreeOn Ω Q Q')
    {Cc Cc' : ℕ → ℕ → LiftCoeff ι h} {t₀ t₁ : ℝ} (hΩ : IsOpen Ω) (hh n : ℕ) {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) (a : ℝ → Vec 2 → ∀ i, h i)
    (h1 : CoeffEqOn Ω Cc Cc' t₀ t₁ hh (n - 1)) (h2 : 2 ≤ n → CoeffEqOn Ω Cc Cc' t₀ t₁ hh (n - 2))
    (h3 : 0 < hh → ∀ k, CoeffEqOn Ω Cc Cc' t₀ t₁ (hh - 1) k) :
    LocEq Ω (liftA Q Cc a hh n t) (liftA Q' Cc' a hh n t) := by
  intro X hX z
  have e1 := cellB1_agree hΩ Q.η hQ.metric Q.v t
    (liftApply_locEq_of hΩ h1 ht (a := a) (a' := a) (fun _ _ => rfl)) X hX z
  have e2 : (if 2 ≤ n then AVRegularity.cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) a t) X z
      else 0) = (if 2 ≤ n then AVRegularity.cellB2 Q.η Q'.G t
        (liftApply (n - 2) (Cc' hh (n - 2)) a t) X z else 0) := by
    by_cases hn2 : 2 ≤ n
    · simp only [hn2, ↓reduceIte]
      exact cellB2_agree hΩ Q.η hQ.metric t
        (liftApply_locEq_of hΩ (h2 hn2) ht (a := a) (a' := a) (fun _ _ => rfl)) X hX z
    · simp only [hn2, ↓reduceIte]
  have e3 : (if hh = 0 then 0 else ∑ j ∈ Finset.range (min Dm n + 1),
      AVRegularity.sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) a t) X z) =
      (if hh = 0 then 0 else ∑ j ∈ Finset.range (min Dm n + 1),
      AVRegularity.sourceCoeff Q'.edge Q.η j t
        (liftApply (n - j) (Cc' (hh - 1) (n - j)) a t) X z) := by
    by_cases hh0 : hh = 0
    · simp only [hh0, ↓reduceIte]
    · simp only [hh0, ↓reduceIte]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact sourceCoeff_agree hΩ hQ.edge Q.η j t (liftApply_locEq_of hΩ
        (h3 (Nat.pos_of_ne_zero hh0) (n - j)) ht (a := a) (a' := a) (fun _ _ => rfl)) X hX z
  show liftA Q Cc a hh n t X z = liftA Q' Cc' a hh n t X z
  unfold liftA
  rw [e1, e2, e3, ← hQ.eta, ← hQ.drift]

theorem liftMean_agree {Dm : ℕ} {Q Q' : LiftOperatorData ι h Dm} (hQ : DataAgreeOn Ω Q Q')
    {Cc Cc' : ℕ → ℕ → LiftCoeff ι h} {t₀ t₁ : ℝ} (hΩ : IsOpen Ω) (hh n : ℕ) {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) (a : ℝ → Vec 2 → ∀ i, h i)
    (h1 : CoeffEqOn Ω Cc Cc' t₀ t₁ hh (n - 1)) (h2 : 2 ≤ n → CoeffEqOn Ω Cc Cc' t₀ t₁ hh (n - 2))
    (h3 : 0 < hh → ∀ k, CoeffEqOn Ω Cc Cc' t₀ t₁ (hh - 1) k) :
    EqOn (liftMean Q Cc a hh n t) (liftMean Q' Cc' a hh n t) Ω := by
  intro X hX
  unfold liftMean
  rw [show (fun z => liftA Q Cc a hh n t X z) = fun z => liftA Q' Cc' a hh n t X z from
    funext (liftA_agree hQ hΩ hh n ht a h1 h2 h3 X hX)]

theorem liftCellSource_agree {Dm : ℕ} {Q Q' : LiftOperatorData ι h Dm} (hQ : DataAgreeOn Ω Q Q')
    {Cc Cc' : ℕ → ℕ → LiftCoeff ι h} {t₀ t₁ : ℝ} (hΩ : IsOpen Ω) (hh n : ℕ) (hn : 1 ≤ n)
    (IH : ∀ hh' n', (hh' < hh ∨ (hh' = hh ∧ n' < n)) → CoeffEqOn Ω Cc Cc' t₀ t₁ hh' n')
    {t : ℝ} (ht : t ∈ Icc t₀ t₁) (a : ℝ → Vec 2 → ∀ i, h i) :
    LocEq Ω (liftCellSource Q Cc a hh n t) (liftCellSource Q' Cc' a hh n t) := by
  intro X hX z
  unfold liftCellSource
  have hA := liftA_agree hQ (Cc := Cc) (Cc' := Cc') hΩ hh n ht a
    (IH hh (n - 1) (Or.inr ⟨rfl, by omega⟩))
    (fun h2 => IH hh (n - 2) (Or.inr ⟨rfl, by omega⟩))
    (fun h0 k => IH (hh - 1) k (Or.inl (by omega))) X hX z
  have hM := liftMean_agree hQ (Cc := Cc) (Cc' := Cc') hΩ hh n ht a
    (IH hh (n - 1) (Or.inr ⟨rfl, by omega⟩))
    (fun h2 => IH hh (n - 2) (Or.inr ⟨rfl, by omega⟩))
    (fun h0 k => IH (hh - 1) k (Or.inl (by omega))) hX
  have hsum : ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean Q Cc a p.2 (n - j)) t X z =
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc' p.1 j) (liftMean Q' Cc' a p.2 (n - j)) t X z := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hj' := Finset.mem_Icc.mp hj
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hmean : EqOn (liftMean Q Cc a p.2 (n - j) t) (liftMean Q' Cc' a p.2 (n - j) t) Ω :=
      liftMean_agree hQ (Cc := Cc) (Cc' := Cc') hΩ p.2 (n - j) ht a
        (IH p.2 (n - j - 1) (by omega))
        (fun h2 => IH p.2 (n - j - 2) (by omega))
        (fun h0 k => IH (p.2 - 1) k (Or.inl (by omega)))
    exact liftApply_locEq (n := j) (B := Cc p.1 j) (B' := Cc' p.1 j)
      (a := liftMean Q Cc a p.2 (n - j)) (a' := liftMean Q' Cc' a p.2 (n - j)) (t := t) hΩ
      (fun m _ α X' hX' => IH p.1 j (by omega) t ht m α X' hX') hmean X hX z
  rw [hA, hM, hsum]

end AVRegularity.Uniqueness
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Uniqueness

/-! Congruence of the finer output of a source in the lift coefficients, and the support of the
partition weights.

The slow flux `liftFluxX`, the path mean flux `pathMeanFlux`, the finer output `fluxOp` and the
transfer `transferAt` depend on the lift coefficients only through their values at the cell time of
the output, and `transferAt` reads them only where the partition weight does not vanish. -/

open AVRegularity

theorem liftFluxX_congr {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ} (Q : LiftOperatorData ι h Dm)
    (Cc Cc' : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (τ : ℝ)
    (hP : ∀ hh' ≤ hh, ∀ n' m' (α : DerivativeWord2 m'), Cc hh' n' m' α τ = Cc' hh' n' m' α τ) :
    liftFluxX Q Cc a hh n τ = liftFluxX Q Cc' a hh n τ := by
  have e1 : liftApply (n - 1) (Cc hh (n - 1)) a τ = liftApply (n - 1) (Cc' hh (n - 1)) a τ :=
    liftApply_congr (fun m _ α => hP hh le_rfl _ m α) rfl
  have e2 : liftApply (n - 2) (Cc hh (n - 2)) a τ = liftApply (n - 2) (Cc' hh (n - 2)) a τ :=
    liftApply_congr (fun m _ α => hP hh le_rfl _ m α) rfl
  have e3 : ∀ j, hh ≠ 0 → liftApply (n - j) (Cc (hh - 1) (n - j)) a τ =
      liftApply (n - j) (Cc' (hh - 1) (n - j)) a τ := fun j hh0 =>
    liftApply_congr (fun m _ α => hP (hh - 1) (by omega) _ m α) rfl
  unfold liftFluxX
  rcases Nat.eq_zero_or_pos hh with hh0 | hh0
  · subst hh0
    simp only [e1, e2, ↓reduceIte]
  · have hne : hh ≠ 0 := Nat.pos_iff_ne_zero.mp hh0
    simp only [e1, e2, e3 _ hne, hne, ↓reduceIte]

theorem pathMeanFlux_congr (D : OCData) (m : ℕ) (ρ : ℝ) {Dm : ℕ} {h : ℕ}
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc Cc' : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ)
    (hP : ∀ hh' ≤ h, ∀ n' m' (α : DerivativeWord2 m'),
      Cc hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) = Cc' hh' n' m' α ((D.cellScaleSq m)⁻¹ * t)) :
    pathMeanFlux D m ρ Q Cc n t = pathMeanFlux D m ρ Q Cc' n t := by
  funext f y k
  unfold pathMeanFlux
  rw [liftFluxX_congr Q Cc Cc' _ h n _ hP]

/-- The partition weight of the slot `k` vanishes outside the window of its pulse. -/
theorem cutoff_support (α q : ℝ) (Λ m : ℕ) (k : ℤ) (t : ℝ) (hτ : 0 < ocTau α q Λ m)
    (h : ocCutoff α q Λ m k t ≠ 0) :
    ((k : ℝ) - 61 / 48) * ocTau α q Λ m ≤ t ∧ t ≤ ((k : ℝ) + 61 / 48) * ocTau α q Λ m := by
  unfold ocCutoff at h
  have hpos : 0 < 5 / 2 - 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m := by
    by_contra hneg
    exact h (Real.smoothTransition.zero_of_nonpos (not_lt.mp hneg))
  have h2 : 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m < 5 / 2 := by linarith
  rw [div_lt_iff₀ hτ] at h2
  have h3 : |t - (k : ℝ) * ocTau α q Λ m| < 5 / 4 * ocTau α q Λ m := by linarith
  have := abs_lt.mp h3
  constructor <;> nlinarith [this.1, this.2]

end AVRegularity.Uniqueness
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Uniqueness

/-! Locality of the finer outputs in the lift coefficients.

With the localized lift relation, two lift families agree only on the open set `Ω` of admissible
slow offsets of each base chain. The transfer reads the finer outputs only through their
coefficients at the label `0` (`fluxCoeff … 0`), and these read the lifts only through their germs
at the slow offset `0 ∈ Ω`:
* `liftFluxX_locEq`, `pathMeanFlux_eq_of_agreeOn`: the slow flux and the path mean flux at a label
  `y` with `ρ⁻¹ y ∈ Ω` read the lifts on `Ω` only;
* `covOperator_iterate_germ`, `pushFlux_germ`: the covariance operator and the push-forward by a
  chart pair fixing `0` preserve germs at `0`;
* `fluxOp_fluxCoeff_congr`: the coefficients at `0` of the finer outputs agree;
* `transferAt_congr_coeff`: the transfer depends on the finer outputs only through these. -/

open AVRegularity

section

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {Ω : Set (Vec 2)}

theorem liftFluxX_locEq {Dm : ℕ} (Q : LiftOperatorData ι h Dm) {Cc Cc' : ℕ → ℕ → LiftCoeff ι h}
    (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (τ : ℝ) (hΩ : IsOpen Ω)
    (hP : ∀ hh' ≤ hh, ∀ n' m' (α : DerivativeWord2 m'), ∀ X ∈ Ω,
      Cc hh' n' m' α τ X = Cc' hh' n' m' α τ X) (κ : Fin 2) :
    LocEq Ω (fun X z => liftFluxX Q Cc a hh n τ X z κ) (fun X z => liftFluxX Q Cc' a hh n τ X z κ) := by
  have e1 : LocEq Ω (liftApply (n - 1) (Cc hh (n - 1)) a τ) (liftApply (n - 1) (Cc' hh (n - 1)) a τ) :=
    liftApply_locEq hΩ (fun m _ α X hX => hP hh le_rfl _ m α X hX) (fun _ _ => rfl)
  have e2 : LocEq Ω (liftApply (n - 2) (Cc hh (n - 2)) a τ) (liftApply (n - 2) (Cc' hh (n - 2)) a τ) :=
    liftApply_locEq hΩ (fun m _ α X hX => hP hh le_rfl _ m α X hX) (fun _ _ => rfl)
  have e3 : ∀ j, hh ≠ 0 → LocEq Ω (liftApply (n - j) (Cc (hh - 1) (n - j)) a τ)
      (liftApply (n - j) (Cc' (hh - 1) (n - j)) a τ) := fun j hh0 =>
    liftApply_locEq hΩ (fun m _ α X hX => hP (hh - 1) (by omega) _ m α X hX) (fun _ _ => rfl)
  intro X hX z
  have f1 : ∀ j, fastPartial j (liftApply (n - 1) (Cc hh (n - 1)) a τ) X z =
      fastPartial j (liftApply (n - 1) (Cc' hh (n - 1)) a τ) X z := fun j => e1.fastPartial j X hX z
  have s2 : ∀ j, slowPartial j (liftApply (n - 2) (Cc hh (n - 2)) a τ) X z =
      slowPartial j (liftApply (n - 2) (Cc' hh (n - 2)) a τ) X z := fun j =>
    (e2.slowPartial hΩ j) X hX z
  show liftFluxX Q Cc a hh n τ X z κ = liftFluxX Q Cc' a hh n τ X z κ
  unfold liftFluxX
  rw [e1 X hX z]
  simp only [f1, s2]
  rcases Nat.eq_zero_or_pos hh with hh0 | hh0
  · subst hh0
    simp
  · have hne : hh ≠ 0 := by omega
    have s3 : ∀ j, (fun ε : ℝ =>
        sourceFlux Q.edge Q.η ε τ (liftApply (n - j) (Cc (hh - 1) (n - j)) a τ) κ X z) =
        fun ε => sourceFlux Q.edge Q.η ε τ (liftApply (n - j) (Cc' (hh - 1) (n - j)) a τ) κ X z :=
      fun j => funext fun ε => ((e3 j hne).sourceFlux hΩ Q.edge Q.η ε τ κ) X hX z
    simp only [hne, ↓reduceIte, s3]

end

theorem pathMeanFlux_eq_of_agreeOn (D : OCData) (m : ℕ) (ρ : ℝ) {Dm h : ℕ}
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc Cc' : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ) {Ω : Set (Vec 2)}
    (hΩ : IsOpen Ω)
    (hP : ∀ hh' ≤ h, ∀ n' m' (α : DerivativeWord2 m'), ∀ X ∈ Ω,
      Cc hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X = Cc' hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X)
    (f : Vec 2 → ℝ) (y : Vec 2) (hy : ρ⁻¹ • y ∈ Ω) :
    pathMeanFlux D m ρ Q Cc n t f y = pathMeanFlux D m ρ Q Cc' n t f y := by
  funext κ
  unfold pathMeanFlux
  rw [show (fun z => liftFluxX Q Cc (fun _ X => Pi.single (0 : Fin (h + 1)) (f (ρ • X))) h n
      ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z κ) =
      (fun z => liftFluxX Q Cc' (fun _ X => Pi.single (0 : Fin (h + 1)) (f (ρ • X))) h n
      ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z κ) from
    funext fun z => liftFluxX_locEq Q _ h n _ hΩ hP κ _ hy z]

theorem pathMeanFlux_germ (D : OCData) (m : ℕ) (ρ : ℝ) {Dm h : ℕ}
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (Cc Cc' : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ) {Ω : Set (Vec 2)}
    (hΩ : IsOpen Ω) (h0 : (0 : Vec 2) ∈ Ω)
    (hP : ∀ hh' ≤ h, ∀ n' m' (α : DerivativeWord2 m'), ∀ X ∈ Ω,
      Cc hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X = Cc' hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X)
    (f : Vec 2 → ℝ) :
    pathMeanFlux D m ρ Q Cc n t f =ᶠ[𝓝 0] pathMeanFlux D m ρ Q Cc' n t f := by
  have hO : IsOpen {y : Vec 2 | ρ⁻¹ • y ∈ Ω} := hΩ.preimage (continuous_const_smul _)
  have h00 : (0 : Vec 2) ∈ {y : Vec 2 | ρ⁻¹ • y ∈ Ω} := by
    show ρ⁻¹ • (0 : Vec 2) ∈ Ω
    rw [smul_zero]; exact h0
  filter_upwards [hO.mem_nhds h00] with y hy
  exact pathMeanFlux_eq_of_agreeOn D m ρ Q Cc Cc' n t hΩ hP f y hy

/-! ### Germs of operators -/

theorem covOperator_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Matrix (Fin 2) (Fin 2) ℝ) {V V' : Vec 2 → E} {x : Vec 2} (hV : V =ᶠ[𝓝 x] V') :
    covOperator H V =ᶠ[𝓝 x] covOperator H V' := by
  have h1 := hV.fderiv (𝕜 := ℝ)
  have hj : ∀ j : Fin 2, (fun y => fderiv ℝ (fun y => fderiv ℝ V y (basisVec j)) y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (fun y => fderiv ℝ V' y (basisVec j)) y) := fun j => by
    have h2 : (fun y => fderiv ℝ V y (basisVec j)) =ᶠ[𝓝 x] (fun y => fderiv ℝ V' y (basisVec j)) :=
      h1.mono fun y hy => by simp only [hy]
    exact h2.fderiv
  filter_upwards [hj 0, hj 1] with y hy0 hy1
  unfold covOperator
  simp only [Fin.sum_univ_two]
  rw [hy0, hy1]

theorem covOperator_iterate_germ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Matrix (Fin 2) (Fin 2) ℝ) {x : Vec 2} :
    ∀ (a : ℕ) {V V' : Vec 2 → E}, V =ᶠ[𝓝 x] V' →
      (covOperator H)^[a] V =ᶠ[𝓝 x] (covOperator H)^[a] V'
  | 0, _, _, hV => hV
  | a + 1, V, V', hV => by
      rw [Function.iterate_succ', Function.comp_apply, Function.comp_apply]
      exact covOperator_germ H (covOperator_iterate_germ H a hV)

theorem pushFlux_germ {Ψ Ψinv : Vec 2 → Vec 2} (hc : ContinuousAt Ψinv 0) (h0 : Ψinv 0 = 0)
    {L L' : (Vec 2 → ℝ) → Vec 2 → Vec 2} (hL : ∀ g, L g =ᶠ[𝓝 0] L' g) (f : Vec 2 → ℝ) :
    pushFlux Ψ Ψinv L f =ᶠ[𝓝 0] pushFlux Ψ Ψinv L' f := by
  have hmem := hc.preimage_mem_nhds (by rw [h0]; exact hL (f ∘ Ψ))
  filter_upwards [hmem] with x hx
  unfold pushFlux
  rw [show L (f ∘ Ψ) (Ψinv x) = L' (f ∘ Ψ) (Ψinv x) from hx]

theorem transferAt_congr_coeff (D : OCData) (m : ℕ) (pc : ℤ) (lam : ℝ) (Dγ : ℕ)
    (fop fop' : FamFluxOp) (t : ℝ) (ch : RealChain) (z : Vec 2) (d' : ℕ)
    (β : DerivativeWord2 (d' - 1))
    (h : ∀ k : ℤ, ocCutoff D.α D.q D.Λ m k t ≠ 0 → ∀ A (d : ℕ) (I : DerivativeWord2 (d - 1)),
      fluxCoeff (fop k t A) d I 0 = fluxCoeff (fop' k t A) d I 0) :
    transferAt D m pc lam Dγ fop t ch z d' β = transferAt D m pc lam Dγ fop' t ch z d' β := by
  unfold transferAt
  congr 1
  refine finsum_congr (fun k => ?_)
  refine finsum_congr (fun hk => ?_)
  by_cases hc : ocCutoff D.α D.q D.Λ m k t = 0
  · simp [hc]
  · have e : (fun d (I : DerivativeWord2 (d - 1)) => fluxCoeff (fop k t (ch.appendChild D k t z)) d I 0) =
        fun d I => fluxCoeff (fop' k t (ch.appendChild D k t z)) d I 0 :=
      funext fun d => funext fun I => h k hc _ d I
    rw [e]

section Stage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {G : GenStage D hr Dm b j₀}

/-- The two lift families agree at the cell time `τ` on the family `A` over the slot `k`, for the
slow offsets of `Ω` (vacuous for the sources without a path). -/
def LiftAgreeOn (s : SuccSource G)
    (Cc Cc' : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)) (k : ℤ)
    (A : RealChain) (τ : ℝ) (Ω : Set (Vec 2)) : Prop :=
  match s, Cc, Cc' with
  | .copyDir .., _, _ => True
  | .letterDiag .., _, _ => True
  | .copyQuad _ h _, Cc, Cc' | .letterMean _ _ h _, Cc, Cc' | .letterCov _ _ h _ _ _, Cc, Cc' =>
      ∀ hh ≤ h, ∀ n' m' (α : DerivativeWord2 m'), ∀ X ∈ Ω,
        Cc k A hh n' m' α τ X = Cc' k A hh n' m' α τ X

open scoped Classical in
/-- **The coefficients at the label `0` of the finer outputs agree** when the lifts agree on an
open set of slow offsets containing `0` (and the inverse chart map of the family fixes `0`,
continuously). -/
theorem fluxOp_fluxCoeff_congr (ρ s₀ : ℝ) (s : SuccSource G)
    (Cc Cc' : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)) (k : ℤ)
    (t : ℝ) (A : RealChain) {Ω : Set (Vec 2)}
    (hΩ : (IsAdmissibleChain D b j₀ G.level k A ∧ Odd k) → IsOpen Ω ∧ (0 : Vec 2) ∈ Ω)
    (hΦ : ContinuousAt (A.famMapInv D t) 0 ∧ A.famMapInv D t 0 = 0)
    (hP : (IsAdmissibleChain D b j₀ G.level k A ∧ Odd k) →
      LiftAgreeOn s Cc Cc' k A ((D.cellScaleSq G.level)⁻¹ * t) Ω)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) :
    fluxCoeff (s.fluxOp ρ s₀ Cc k t A) d I 0 = fluxCoeff (s.fluxOp ρ s₀ Cc' k t A) d I 0 := by
  by_cases hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k
  · have hP := hP hA
    obtain ⟨hΩ, h0⟩ := hΩ hA
    have h00 : ρ⁻¹ • (0 : Vec 2) ∈ Ω := by rw [smul_zero]; exact h0
    cases s with
    | copyDir t' v u γ => simp only [SuccSource.fluxOp, hA, and_self, ↓reduceDIte]
    | letterDiag t' u => simp only [SuccSource.fluxOp, hA, and_self, ↓reduceDIte]
    | copyQuad t' h π =>
      simp only [SuccSource.fluxOp, hA, and_self, ↓reduceDIte]
      unfold fluxCoeff
      rw [pathMeanFlux_eq_of_agreeOn D G.level ρ _ _ _ 2 t hΩ hP _ 0 h00]
    | letterMean t' n h π =>
      have hpm := pathMeanFlux_eq_of_agreeOn D G.level ρ
        (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩)) (Cc k A) (Cc' k A) n t
        hΩ hP (fun Y => ∏ j, (Y - 0) (I j)) 0 h00
      simp only [SuccSource.fluxOp, hA, and_self, ↓reduceDIte]
      unfold fluxCoeff
      simp only [hpm]
    | letterCov t' n h a a' π =>
      simp only [SuccSource.fluxOp, hA, and_self, ↓reduceDIte]
      unfold fluxCoeff pullFlux
      have hgerm := covOperator_iterate_germ
        (ocCovariance D.α D.q D.Λ D.ζ G.level (D.κ G.level) (D.κ (G.level - 1)) s₀ t) a
        (pushFlux_germ (Ψ := A.famMap D t) hΦ.1 hΦ.2
          (fun g => pathMeanFlux_germ D G.level ρ
            (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩)) _ _ n t hΩ h0 hP g)
          ((SuccSource.covAt D G.level s₀ t)^[a'] ((fun Y => ∏ j, (Y - 0) (I j)) ∘ A.famMapInv D t)))
      have hΦ0 : A.famMap D t 0 = 0 := by simp [RealChain.famMap]
      simp only [SuccSource.covAtFlux]
      rw [hΦ0, hgerm.eq_of_nhds]
  · simp only [SuccSource.fluxOp, hA, ↓reduceDIte]

end Stage

end AVRegularity.Uniqueness
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Uniqueness

/-! Conditional uniqueness of the coefficients of the next family.

`successor_flux_unique_of_window_data` is the structural part of `successor_flux_unique`: the
provenance of an identity of an actual successor determines its source (`succSource_eq_of_prov`),
the transferred coefficient reads the lifts of the path family only at the cell times of the
window of the pulse (`cutoff_support`), and only through their germs at the slow offset `0`
(`fluxOp_fluxCoeff_congr`), where, granted the window data of the molecular metric and the drift
(`SuccWindowData`), the localized lift sequence is unique on the open set of admissible slow
offsets (`AVRegularity.Uniqueness.lift_sequence_unique_window_on`). The window data is not proved here: it
is the ellipticity of the molecular metric `F⁻¹F⁻ᵀ` and the boundedness of the pulse drift on the
window of the pulse, for every admissible odd chain, together with `0 ≤ cellScaleSq` (the sign of
the diffusivity `κ`; for `cellScaleSq < 0` the cell window is empty and the lifts are not
determined). The positivity of the time scale `τ_m` follows from the naturality of the stage
(`ocTau_pos_of_natural`). -/

open AVRegularity

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The window data (ellipticity and boundedness of the metric and the drift of the cell operator,
at each slow point) of the lift operators of all scalar path families of the stage `G`, on the
cell-time window of the pulse, for every admissible odd chain, together with `0 ≤ cellScaleSq` (the sign of
the diffusivity `κ`; for `cellScaleSq < 0` the cell window is empty and the lifts are not
determined). The positivity of the time scale `τ_m` follows from the naturality of the stage
(`ocTau_pos_of_natural`). -/
def SuccWindowData (D : OCData) (b : ℝ) (j₀ : ℕ) (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) :
    Prop :=
  ∀ (h : ℕ) (π : StagePath G h) (k : ℤ) (A : RealChain)
    (hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k) (X : Vec 2),
    ∃ lo A' Mv : ℝ, WindowData
      (fun t => Matrix.of ((familyLiftData D G.level k A (Mn.lenFactor * liftLength D G.level)
        (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩)).G t X))
      (familyLiftData D G.level k A (Mn.lenFactor * liftLength D G.level)
        (pathEdges G π ⟨k, hA.2⟩ ⟨A, hA.1⟩)).v
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) lo A' Mv

theorem liftAgreeOn_of_window {G : GenStage D hr Dm b j₀} (Mn : SuccMenu)
    (hcs : 0 ≤ D.cellScaleSq G.level) (hτ : 0 < ocTau D.α D.q D.Λ G.level)
    (hW : AVRegularity.Uniqueness.SuccWindowData D b j₀ Mn G) (s : SuccSource G)
    (Cc Cc' : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hLF : s.IsLiftFamily Mn Cc) (hLF' : s.IsLiftFamily Mn Cc') (k : ℤ) (A : RealChain)
    (hA : IsAdmissibleChain D b j₀ G.level k A ∧ Odd k)
    (hΩ : IsOpen (ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level))) (τ : ℝ)
    (hτw : τ ∈ Set.Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)) :
    LiftAgreeOn s Cc Cc' k A τ (ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level)) := by
  have hab : D.slotStart G.level k / D.cellScaleSq G.level ≤
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) := by
    unfold OCData.slotStart
    apply div_le_div_of_nonneg_right _ hcs
    nlinarith
  cases s with
  | copyDir t v u γ => trivial
  | letterDiag t u => trivial
  | copyQuad t h π =>
    have hu := lift_sequence_unique_window_on _ _ _ hab hΩ (fun X _ => hW h π k A hA X) Mn.sX
      Mn.sZ Mn.N h (Cc k A) (Cc' k A) (hLF k A hA) (hLF' k A hA)
    intro hh hhle n' m' α X hX
    funext z v u
    exact hu hh hhle n' m' α τ hτw X hX z v u
  | letterMean t n h π =>
    have hu := lift_sequence_unique_window_on _ _ _ hab hΩ (fun X _ => hW h π k A hA X) Mn.sX
      Mn.sZ Mn.N h (Cc k A) (Cc' k A) (hLF k A hA) (hLF' k A hA)
    intro hh hhle n' m' α X hX
    funext z v u
    exact hu hh hhle n' m' α τ hτw X hX z v u
  | letterCov t n h a a' π =>
    have hu := lift_sequence_unique_window_on _ _ _ hab hΩ (fun X _ => hW h π k A hA X) Mn.sX
      Mn.sZ Mn.N h (Cc k A) (Cc' k A) (hLF k A hA) (hLF' k A hA)
    intro hh hhle n' m' α X hX
    funext z v u
    exact hu hh hhle n' m' α τ hτw X hX z v u


theorem ocTau_nonneg (α q : ℝ) (Λ m : ℕ) : 0 ≤ ocTau α q Λ m := by
  unfold ocTau ocTauPP ocL
  positivity

/-- A natural stage has positive time scale `τ_m`: its weights are the partition of unity of the
slots, whose windows `[(k - 61/48)τ_m, (k + 61/48)τ_m]` are locally finite. -/
theorem ocTau_pos_of_natural {M : ℕ} {G : GenStage D hr Dm b j₀} (hnat : G.IsNatural M) :
    0 < ocTau D.α D.q D.Λ G.level := by
  refine lt_of_le_of_ne (ocTau_nonneg _ _ _ _) (fun h0 => ?_)
  have hfin := G.fam.locally_finite 0 0
  have hmem : ∀ p : OddSlot, p ∈ {p | ((G.fam.piece p).output ∩ Set.Icc (0 : ℝ) 0).Nonempty} := by
    intro p
    refine ⟨0, ?_, Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩⟩
    rw [(hnat.1 p).2.1]
    unfold ocPulseWindow
    rw [← h0]
    simp
  have hinf : Infinite OddSlot :=
    Infinite.of_injective (fun n : ℕ => (⟨2 * (n : ℤ) + 1, ⟨n, rfl⟩⟩ : OddSlot)) (by
      intro n n' h
      have := congrArg Subtype.val h
      simp only at this
      exact_mod_cast (by omega : (n : ℤ) = n'))
  have : Set.univ ⊆ {p : OddSlot | ((G.fam.piece p).output ∩ Set.Icc (0 : ℝ) 0).Nonempty} :=
    fun p _ => hmem p
  exact Set.infinite_univ (hfin.subset this)

/-- **Conditional uniqueness of the transferred coefficients of the next family**: the statement of
`successor_flux_unique`, granted `0 ≤ cellScaleSq` and the window data of the lift operators
(`SuccWindowData`). -/
theorem successor_flux_unique_of_window_data (P : ProvParams)
    (Mn : SuccMenu) (M : ℕ) (G G₁ G₂ : GenStage D hr Dm b j₀) (hnat : G.IsNatural M)
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (h₁ : IsActualSuccessor D P Mn G G₁)
    (h₂ : IsActualSuccessor D P Mn G G₂) (v₁ u₁ : CompIn G₁.comps) (γ₁ : G₁.fam.Γ v₁ u₁)
    (v₂ u₂ : CompIn G₂.comps) (γ₂ : G₂.fam.Γ v₂ u₂) (hv : v₁.1 = v₂.1) (hu : u₁.1 = u₂.1)
    (hγ : G₁.prov v₁ u₁ γ₁ = G₂.prov v₂ u₂ γ₂)
    (hnd : ∀ m', G₁.prov v₁ u₁ γ₁ ≠ Prov.letter m' .diag []) (p : OddSlot)
    (c₁ : StageCtx D b j₀ G₁.level p) (c₂ : StageCtx D b j₀ G₂.level p) (hc : c₁.1 = c₂.1)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2) (hd : 2 ≤ d)
    (hcs : 0 ≤ D.cellScaleSq G.level) (hW : AVRegularity.Uniqueness.SuccWindowData D b j₀ Mn G)
    (hΩ : ∀ k A, IsAdmissibleChain D b j₀ G.level k A →
      IsOpen (ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level)) ∧
        (0 : Vec 2) ∈ ladderOmega D b j₀ G.level k A (Mn.lenFactor * liftLength D G.level))
    (hΦ : ∀ (A : RealChain) (t : ℝ), ContinuousAt (A.famMapInv D t) 0 ∧ A.famMapInv D t 0 = 0) :
    G₁.fam.flux p c₁ v₁ u₁ γ₁ d I t X z = G₂.fam.flux p c₂ v₂ u₂ γ₂ d I t X z := by
  have hτ := ocTau_pos_of_natural hnat
  obtain ⟨hl1, hlev1, hcomps1, hnat1, htag1, -, e₁, Cc₁, Cc0₁, hLF₁, hDL₁, hmain₁⟩ := h₁
  obtain ⟨hl2, hlev2, hcomps2, hnat2, htag2, -, e₂, Cc₂, Cc0₂, hLF₂, hDL₂, hmain₂⟩ := h₂
  have hlev : G₁.level = G₂.level := by omega
  obtain ⟨hp1, hmap1, hflux1, hflux1'⟩ := hmain₁ v₁ u₁ γ₁
  obtain ⟨hp2, hmap2, hflux2, hflux2'⟩ := hmain₂ v₂ u₂ γ₂
  have hs : (e₁ v₁ u₁ γ₁).1 = (e₂ v₂ u₂ γ₂).1 := by
    refine succSource_eq_of_prov hl1 hnat.2.2.2 hold _ _ (e₁ v₁ u₁ γ₁).2.1 (e₂ v₂ u₂ γ₂).2.1
      (hp1.symm.trans (hγ.trans hp2)) ?_ ?_
    · rw [(e₁ v₁ u₁ γ₁).2.2.1, (e₂ v₂ u₂ γ₂).2.2.1, hu]
    · rw [(e₁ v₁ u₁ γ₁).2.2.2, (e₂ v₂ u₂ γ₂).2.2.2, hv]
  have hdiag : ∀ s : SuccSource G, s.prov G.level = G₁.prov v₁ u₁ γ₁ → ¬ s.IsDiag := by
    intro s hp hdg
    cases s <;> simp only [SuccSource.IsDiag] at hdg
    exact hnd G.level (by rw [← hp]; rfl)
  have hnd1 : ¬ (e₁ v₁ u₁ γ₁).1.IsDiag := hdiag _ hp1.symm
  have hnd2 : ¬ (e₂ v₂ u₂ γ₂).1.IsDiag := by
    exact hdiag _ (hp2.symm.trans hγ.symm)
  have e1 := hflux1 hnd1 p c₁ d I t X z hd
  have e2 := hflux2 hnd2 p c₂ d I t X z hd
  have hrec : RealChain.recenter D (↑c₁) (D.eps (G₁.level - 1) • X) =
      RealChain.recenter D (↑c₂) (D.eps (G₂.level - 1) • X) := by rw [hc, hlev]
  have hadm' : IsAdmissibleChain D b j₀ G₁.level (↑p) (RealChain.recenter D (↑c₂) (D.eps (G₂.level - 1) • X)) =
      IsAdmissibleChain D b j₀ G₂.level (↑p) (RealChain.recenter D (↑c₂) (D.eps (G₂.level - 1) • X)) := by
    rw [hlev]
  rw [e1, e2, ← hs, hrec, hadm']
  by_cases hadm : IsAdmissibleChain D b j₀ G₂.level (↑p)
      (RealChain.recenter D (↑c₂) (D.eps (G₂.level - 1) • X))
  · simp only [hadm, ↓reduceIte]
    refine transferAt_congr_coeff D G.level (↑p) _ _ _ _ t _ z d I (fun k hk A d' I' => ?_)
    refine fluxOp_fluxCoeff_congr _ _ _ _ _ k t A (fun hA => hΩ k A hA.1) (hΦ A t)
      (fun hA => ?_) d' I'
    have hsupp := cutoff_support D.α D.q D.Λ G.level k t hτ hk
    refine liftAgreeOn_of_window Mn hcs hτ hW _ _ _ (hLF₁ _) (hs ▸ hLF₂ _) k A hA
      (hΩ k A hA.1).1 _ ?_
    rcases hcs.eq_or_lt with hc0 | hcpos
    · rw [← hc0]
      simp
    · constructor
      · unfold OCData.slotStart
        rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left hsupp.1 (inv_nonneg.mpr hcpos.le)
      · rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left hsupp.2 (inv_nonneg.mpr hcpos.le)
  · simp only [hadm, ↓reduceIte]

end AVRegularity.Uniqueness
end
end
