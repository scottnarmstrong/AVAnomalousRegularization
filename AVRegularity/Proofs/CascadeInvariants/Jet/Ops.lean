-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.Op.Chart
import AVRegularity.Proofs.GenSem.Op.FamChart
public import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev Filter Topology
open scoped NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, sized jets (generic).** The quantitative twin of `RepAlg`/`JetRepG`
(`Providers/GenSem/Jet/JetRepG.lean`), for the ledger of the covariance letters and of the first
source.

`RepAlgQ R`: a graded algebra of represented scalar functions of the index, `R F r C` meaning
"`F` is represented with the cost `r` (reserve units) and the size `C`"; closed under constants,
sums and products, monotone in the cost and in the size.

`JetRepGQ R σ n g r C`: the value at the label `0` of the label functions `g l` is represented
with cost `r` and size `C`, and recursively the jets of order `n - 1` of the first derivatives
with cost `r + 1` and size `σ C`: **one label derivative costs one reserve unit and the factor
`σ`**. Hence an ordered derivative of order `m ≤ n` at `0` has cost `r + m` and size `σ^m C`
(`JetRepGQ.orderedDerivative`). Closure: germs, monotonicity, constants, sums, scalar multiples,
products (`2^n C₁ C₂`, Leibniz), finite sums. All sizes are products of the input sizes and of
constants depending only on the order: the sizes of composite expressions stay multiplicative. -/

section
open AVRegularity.Providers.GenSem

/-- A graded algebra of represented scalar functions of the index, with costs and sizes. -/
structure RepAlgQ {Λ : Type*} (R : (Λ → ℝ) → ℕ → ℝ≥0 → Prop) : Prop where
  mono : ∀ {F : Λ → ℝ} {r r' : ℕ} {C C' : ℝ≥0}, R F r C → r ≤ r' → C ≤ C' → R F r' C'
  const : ∀ c : ℝ, R (fun _ => c) 0 (Real.toNNReal |c|)
  add : ∀ {F G : Λ → ℝ} {r : ℕ} {C₁ C₂ : ℝ≥0}, R F r C₁ → R G r C₂ →
    R (fun l => F l + G l) r (C₁ + C₂)
  mul : ∀ {F G : Λ → ℝ} {r : ℕ} {C₁ C₂ : ℝ≥0}, R F r C₁ → R G r C₂ →
    R (fun l => F l * G l) r (C₁ * C₂)

namespace RepAlgQ

variable {Λ : Type*} {R : (Λ → ℝ) → ℕ → ℝ≥0 → Prop} (hR : RepAlgQ R)
include hR

theorem zero (r : ℕ) : R (fun _ => (0 : ℝ)) r 0 :=
  hR.mono (hR.const 0) (Nat.zero_le r) (by simp)

theorem const' (c : ℝ) (r : ℕ) {C : ℝ≥0} (hC : Real.toNNReal |c| ≤ C) : R (fun _ => c) r C :=
  hR.mono (hR.const c) (Nat.zero_le r) hC

theorem smul {F : Λ → ℝ} {r : ℕ} {C : ℝ≥0} (h : R F r C) (c : ℝ) :
    R (fun l => c * F l) r (Real.toNNReal |c| * C) :=
  hR.mul (hR.const' c r le_rfl) h

theorem finsetSum {κ : Type*} (s : Finset κ) {F : κ → Λ → ℝ} {r : ℕ} {C : κ → ℝ≥0}
    (h : ∀ k ∈ s, R (F k) r (C k)) : R (fun l => ∑ k ∈ s, F k l) r (∑ k ∈ s, C k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hR.zero r
  | insert a s ha ih =>
    have := hR.add (h a (Finset.mem_insert_self a s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
    simpa [Finset.sum_insert ha] using this

end RepAlgQ

variable {Λ : Type*} {R : (Λ → ℝ) → ℕ → ℝ≥0 → Prop} {σ : ℝ≥0}

variable (R σ) in
/-- Sized jets of order `n` at the label `0`: cost `r` and size `C` for the value, one more
reserve unit and the factor `σ` for each derivative. -/
def JetRepGQ : ℕ → (Λ → Vec 2 → ℝ) → ℕ → ℝ≥0 → Prop
  | 0, g, r, C => R (fun l => g l 0) r C
  | n + 1, g, r, C => R (fun l => g l 0) r C ∧ ∀ j, JetRepGQ n (dLabelG j g) (r + 1) (σ * C)

theorem JetRepGQ.value {n : ℕ} {g : Λ → Vec 2 → ℝ} {r : ℕ} {C : ℝ≥0}
    (h : JetRepGQ R σ n g r C) : R (fun l => g l 0) r C := by
  cases n with
  | zero => exact h
  | succ n => exact h.1

theorem JetRepGQ.mono (hR : RepAlgQ R) : ∀ {n n' : ℕ}, n' ≤ n → ∀ {g : Λ → Vec 2 → ℝ}
    {r r' : ℕ} {C C' : ℝ≥0}, JetRepGQ R σ n g r C → r ≤ r' → C ≤ C' → JetRepGQ R σ n' g r' C'
  | _, 0, _, _, _, _, _, _, h, hr, hC => hR.mono h.value hr hC
  | 0, _ + 1, hn, _, _, _, _, _, _, _, _ => absurd hn (by omega)
  | _ + 1, _ + 1, hn, _, _, _, _, _, h, hr, hC =>
      ⟨hR.mono h.1 hr hC, fun j => JetRepGQ.mono hR (by omega) (h.2 j) (by omega)
        (mul_le_mul' le_rfl hC)⟩

/-- Jets depend only on the germs at `0`. -/
theorem JetRepGQ.congr_germ : ∀ {n : ℕ} {g h : Λ → Vec 2 → ℝ} {r : ℕ} {C : ℝ≥0},
    JetRepGQ R σ n g r C → (∀ l, g l =ᶠ[𝓝 0] h l) → JetRepGQ R σ n h r C
  | 0, g, h, r, C, hg, he => by
      have e : (fun l => h l 0) = fun l => g l 0 := funext fun l => ((he l).eq_of_nhds).symm
      show R (fun l => h l 0) r C
      rw [e]
      exact hg
  | _ + 1, g, h, r, C, hg, he => ⟨by
      have e : (fun l => h l 0) = fun l => g l 0 := funext fun l => ((he l).eq_of_nhds).symm
      rw [e]
      exact hg.1, fun j =>
      JetRepGQ.congr_germ (hg.2 j) fun l => by
        have := (he l).fderiv (𝕜 := ℝ)
        filter_upwards [this] with y hy
        simp only [dLabelG, hy]⟩

/-- **Every ordered derivative of order `m ≤ n` at `0`** has cost `r + m` and size `σ^m C`. -/
theorem JetRepGQ.orderedDerivative (hR : RepAlgQ R) : ∀ {n : ℕ} {g : Λ → Vec 2 → ℝ} {r : ℕ}
    {C : ℝ≥0}, JetRepGQ R σ n g r C → ∀ {m : ℕ}, m ≤ n → ∀ α : DerivativeWord2 m,
      R (fun l => AVRegularity.orderedDerivative α (g l) 0) (r + m) (σ ^ m * C)
  | _, g, r, C, h, 0, _, α => by
      have : α = Fin.elim0 := Subsingleton.elim _ _
      subst this
      have e : (fun l => AVRegularity.orderedDerivative (Fin.elim0 : DerivativeWord2 0) (g l) 0) =
          fun l => g l 0 := funext fun l => by simp [AVRegularity.orderedDerivative]
      rw [e]
      simpa using h.value
  | 0, _, _, _, _, _ + 1, hm, _ => absurd hm (by omega)
  | _ + 1, g, r, C, h, m + 1, hm, α => by
      have := JetRepGQ.orderedDerivative hR (h.2 (α 0)) (m := m) (by omega) (fun i => α i.succ)
      have e : (fun l => AVRegularity.orderedDerivative α (g l) 0) =
          fun l => AVRegularity.orderedDerivative (fun i => α i.succ) (dLabelG (α 0) g l) 0 :=
        funext fun l => by rw [orderedDerivative_succ]; rfl
      rw [e]
      exact hR.mono this (by omega) (le_of_eq (by ring))

theorem jetRepGQ_zero (hR : RepAlgQ R) :
    ∀ (n r : ℕ), JetRepGQ R σ n (fun (_ : Λ) (_ : Vec 2) => (0 : ℝ)) r 0
  | 0, r => hR.zero r
  | n + 1, r => ⟨hR.zero r, fun j => by
      rw [mul_zero]
      exact (jetRepGQ_zero hR n (r + 1)).congr_germ fun _ =>
        Filter.Eventually.of_forall fun y => by simp [dLabelG]⟩

/-- A function constant in the label with a represented value has sized jets. -/
theorem jetRepGQ_labelConst (hR : RepAlgQ R) {F : Λ → ℝ} {r : ℕ} {C : ℝ≥0} (hF : R F r C) :
    ∀ n : ℕ, JetRepGQ R σ n (fun l (_ : Vec 2) => F l) r C
  | 0 => hF
  | n + 1 => ⟨hF, fun j =>
      ((jetRepGQ_zero hR n (r + 1)).mono hR le_rfl le_rfl (zero_le)).congr_germ fun l =>
        Filter.Eventually.of_forall fun y => by simp [dLabelG]⟩

theorem jetRepGQ_const (hR : RepAlgQ R) (n : ℕ) (c : ℝ) (r : ℕ) :
    JetRepGQ R σ n (fun (_ : Λ) (_ : Vec 2) => c) r (Real.toNNReal |c|) :=
  jetRepGQ_labelConst hR (hR.const' c r le_rfl) n

/-- Sums. -/
theorem JetRepGQ.add (hR : RepAlgQ R) : ∀ {n : ℕ} {g h : Λ → Vec 2 → ℝ} {r : ℕ} {C₁ C₂ : ℝ≥0},
    (∀ l, ContDiff ℝ n (g l)) → (∀ l, ContDiff ℝ n (h l)) →
    JetRepGQ R σ n g r C₁ → JetRepGQ R σ n h r C₂ →
      JetRepGQ R σ n (fun l y => g l y + h l y) r (C₁ + C₂)
  | 0, _, _, _, _, _, _, _, hg, hh => hR.add hg hh
  | n + 1, g, h, r, C₁, C₂, cg, ch, hg, hh => ⟨hR.add hg.1 hh.1, fun j => by
      have h1 := JetRepGQ.add hR (n := n) (g := dLabelG j g) (h := dLabelG j h)
        (fun l => contDiff_dLabel (cg l) j) (fun l => contDiff_dLabel (ch l) j)
        (hg.2 j) (hh.2 j)
      rw [mul_add]
      refine h1.congr_germ fun l => Filter.Eventually.of_forall fun y => ?_
      simp only [dLabelG]
      rw [fderiv_fun_add ((cg l).differentiable (by norm_cast) y)
        ((ch l).differentiable (by norm_cast) y)]
      rfl⟩

/-- Scalar multiples. -/
theorem JetRepGQ.smul (hR : RepAlgQ R) (c : ℝ) : ∀ {n : ℕ} {g : Λ → Vec 2 → ℝ} {r : ℕ}
    {C : ℝ≥0}, (∀ l, ContDiff ℝ n (g l)) → JetRepGQ R σ n g r C →
      JetRepGQ R σ n (fun l y => c * g l y) r (Real.toNNReal |c| * C)
  | 0, _, _, _, _, hg => hR.smul hg c
  | n + 1, g, r, C, cg, hg => ⟨hR.smul hg.1 c, fun j => by
      have h1 := JetRepGQ.smul hR c (n := n) (g := dLabelG j g)
        (fun l => contDiff_dLabel (cg l) j) (hg.2 j)
      rw [mul_left_comm]
      refine h1.congr_germ fun l => Filter.Eventually.of_forall fun y => ?_
      simp only [dLabelG]
      rw [fderiv_const_mul ((cg l).differentiable (by norm_cast) y)]
      rfl⟩

/-- Products (Leibniz): the size is `2^n C₁ C₂`. -/
theorem JetRepGQ.mul (hR : RepAlgQ R) : ∀ {n : ℕ} {g h : Λ → Vec 2 → ℝ} {r : ℕ} {C₁ C₂ : ℝ≥0},
    (∀ l, ContDiff ℝ n (g l)) → (∀ l, ContDiff ℝ n (h l)) →
    JetRepGQ R σ n g r C₁ → JetRepGQ R σ n h r C₂ →
      JetRepGQ R σ n (fun l y => g l y * h l y) r (2 ^ n * (C₁ * C₂))
  | 0, _, _, _, _, _, _, _, hg, hh => by
      have := hR.mul hg hh
      simpa [JetRepGQ] using this
  | n + 1, g, h, r, C₁, C₂, cg, ch, hg, hh => ⟨by
      refine hR.mono (hR.mul hg.1 hh.1) le_rfl ?_
      calc C₁ * C₂ = 1 * (C₁ * C₂) := (one_mul _).symm
        _ ≤ 2 ^ (n + 1) * (C₁ * C₂) := mul_le_mul' (one_le_pow₀ (by norm_num)) le_rfl, fun j => by
      have cg' : ∀ l, ContDiff ℝ n (g l) := fun l => (cg l).of_le (by norm_cast; omega)
      have ch' : ∀ l, ContDiff ℝ n (h l) := fun l => (ch l).of_le (by norm_cast; omega)
      have cdg : ∀ l, ContDiff ℝ n (dLabelG j g l) := fun l => contDiff_dLabel (cg l) j
      have cdh : ∀ l, ContDiff ℝ n (dLabelG j h l) := fun l => contDiff_dLabel (ch l) j
      have h1 := JetRepGQ.mul hR cdg ch' (hg.2 j) (hh.mono hR (by omega) (by omega) le_rfl)
      have h2 := JetRepGQ.mul hR cg' cdh (hg.mono hR (by omega) (by omega) le_rfl) (hh.2 j)
      have h3 := JetRepGQ.add hR (fun l => (cdg l).mul (ch' l)) (fun l => (cg' l).mul (cdh l))
        h1 h2
      have e : 2 ^ n * (σ * C₁ * C₂) + 2 ^ n * (C₁ * (σ * C₂)) = σ * (2 ^ (n + 1) * (C₁ * C₂)) := by
        ring
      rw [← e]
      refine h3.congr_germ fun l => Filter.Eventually.of_forall fun y => ?_
      simp only [dLabelG]
      rw [fderiv_fun_mul ((cg l).differentiable (by norm_cast) y)
        ((ch l).differentiable (by norm_cast) y)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring⟩

/-- Finite sums. -/
theorem JetRepGQ.finsetSum (hR : RepAlgQ R) {n : ℕ} {κ : Type*} (s : Finset κ)
    {F : κ → Λ → Vec 2 → ℝ} {r : ℕ} {C : κ → ℝ≥0} (hc : ∀ k ∈ s, ∀ l, ContDiff ℝ n (F k l))
    (h : ∀ k ∈ s, JetRepGQ R σ n (F k) r (C k)) :
    JetRepGQ R σ n (fun l y => ∑ k ∈ s, F k l y) r (∑ k ∈ s, C k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact (jetRepGQ_zero hR n r).congr_germ fun l =>
      Filter.Eventually.of_forall fun y => by simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (JetRepGQ.add hR (hc a (Finset.mem_insert_self a s))
      (fun l => ContDiff.sum fun k hk => hc k (Finset.mem_insert_of_mem hk) l)
      (h a (Finset.mem_insert_self a s))
      (ih (fun k hk => hc k (Finset.mem_insert_of_mem hk))
        fun k hk => h k (Finset.mem_insert_of_mem hk))).congr_germ fun l =>
        Filter.Eventually.of_forall fun y => by simp only [Finset.sum_insert ha]
end

/-! **Ledger, sized jets: the chain rule.** For label maps `Ψ` with `Ψ 0 = 0` whose first
derivatives have sized jets of size `P` (a dimensionless Jacobian bound), `g ∘ Ψ` has sized jets of
size `compC P n · C` (`JetRepGQ.comp`): the size stays linear in the size `C` of `g`. -/

section
open AVRegularity.Providers.GenSem

variable {Λ : Type*} {R : (Λ → ℝ) → ℕ → ℝ≥0 → Prop} {σ : ℝ≥0}

/-- The constant of the chain rule of order `n` for a Jacobian bound `P`. -/
def compC (P : ℝ≥0) : ℕ → ℝ≥0
  | 0 => 1
  | n + 1 => 2 * (2 ^ n * (compC P n * P)) + 1

theorem one_le_compC (P : ℝ≥0) : ∀ n, 1 ≤ compC P n
  | 0 => le_rfl
  | _ + 1 => le_add_self

/-- **The chain rule for sized jets**: `g ∘ Ψ` for label maps with `Ψ 0 = 0`. The jets of order
`n` of the composition use the jets of order `n - 1` of the first derivatives of `Ψ`. -/
theorem JetRepGQ.comp' (hR : RepAlgQ R) : ∀ {n : ℕ} {g : Λ → Vec 2 → ℝ}
    {Ψ : Λ → Vec 2 → Vec 2} {r : ℕ} {C P : ℝ≥0},
    (∀ l, Ψ l 0 = 0) → (∀ l, ContDiff ℝ n (g l)) → (∀ l, ContDiff ℝ n (Ψ l)) →
    JetRepGQ R σ n g r C →
    (∀ b j, JetRepGQ R σ (n - 1) (dLabelG j (fun l y => Ψ l y b)) (r + 1) P) →
      JetRepGQ R σ n (fun l y => g l (Ψ l y)) r (compC P n * C)
  | 0, g, Ψ, r, C, P, h0, _, _, hg, _ => by
      have e : (fun l => g l (Ψ l 0)) = fun l => g l 0 := funext fun l => by rw [h0 l]
      show R (fun l => g l (Ψ l 0)) r (compC P 0 * C)
      rw [e]
      have hv : R (fun l => g l 0) r C := hg
      simpa [compC] using hv
  | n + 1, g, Ψ, r, C, P, h0, cg, cΨ, hg, hΨ => ⟨by
      have e : (fun l => g l (Ψ l 0)) = fun l => g l 0 := funext fun l => by rw [h0 l]
      rw [e]
      refine hR.mono hg.1 le_rfl ?_
      calc C = 1 * C := (one_mul C).symm
        _ ≤ compC P (n + 1) * C := mul_le_mul' (one_le_compC P (n + 1)) le_rfl, fun j => by
      have cΨ' : ∀ l, ContDiff ℝ n (Ψ l) := fun l => (cΨ l).of_le (by norm_cast; omega)
      have cΨb : ∀ b l, ContDiff ℝ (n + 1 : ℕ) (fun y => Ψ l y b) := fun b l =>
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) b).contDiff.comp (cΨ l)
      have hΨn : ∀ b j, JetRepGQ R σ n (dLabelG j (fun l y => Ψ l y b)) (r + 1) P :=
        fun b j => hΨ b j
      have hΨ' : ∀ b j, JetRepGQ R σ (n - 1) (dLabelG j (fun l y => Ψ l y b)) (r + 1 + 1) P :=
        fun b j => (hΨn b j).mono hR (Nat.sub_le n 1) (by omega) le_rfl
      have hterm : ∀ b, JetRepGQ R σ n
          (fun l y => dLabelG b g l (Ψ l y) * dLabelG j (fun l y => Ψ l y b) l y) (r + 1)
          (2 ^ n * (compC P n * (σ * C) * P)) := by
        intro b
        have h1 := JetRepGQ.comp' hR h0 (fun l => contDiff_dLabel (cg l) b) cΨ' (hg.2 b) hΨ'
        exact JetRepGQ.mul hR (fun l => (contDiff_dLabel (cg l) b).comp (cΨ' l))
          (fun l => contDiff_dLabel (cΨb b l) j) h1 (hΨn b j)
      have hsum := JetRepGQ.add hR (fun l => ((contDiff_dLabel (cg l) 0).comp (cΨ' l)).mul
          (contDiff_dLabel (cΨb 0 l) j))
        (fun l => ((contDiff_dLabel (cg l) 1).comp (cΨ' l)).mul
          (contDiff_dLabel (cΨb 1 l) j)) (hterm 0) (hterm 1)
      have hle : 2 ^ n * (compC P n * (σ * C) * P) + 2 ^ n * (compC P n * (σ * C) * P) ≤
          σ * (compC P (n + 1) * C) := by
        have e : 2 ^ n * (compC P n * (σ * C) * P) + 2 ^ n * (compC P n * (σ * C) * P) + σ * C =
            σ * (compC P (n + 1) * C) := by
          simp only [compC]
          ring
        exact le_self_add.trans_eq e
      refine (hsum.mono hR le_rfl le_rfl hle).congr_germ fun l =>
        Filter.Eventually.of_forall fun y => ?_
      simp only [dLabelG]
      rw [fderiv_comp_label ((cg l).differentiable (by norm_cast) _)
        ((cΨ l).differentiable (by norm_cast) y) j, Fin.sum_univ_two]
      rfl⟩

/-- The chain rule, with the jets of the first derivatives of `Ψ` to the same order. -/
theorem JetRepGQ.comp (hR : RepAlgQ R) {n : ℕ} {g : Λ → Vec 2 → ℝ} {Ψ : Λ → Vec 2 → Vec 2}
    {r : ℕ} {C P : ℝ≥0} (h0 : ∀ l, Ψ l 0 = 0) (cg : ∀ l, ContDiff ℝ n (g l))
    (cΨ : ∀ l, ContDiff ℝ n (Ψ l)) (hg : JetRepGQ R σ n g r C)
    (hΨ : ∀ b j, JetRepGQ R σ n (dLabelG j (fun l y => Ψ l y b)) (r + 1) P) :
    JetRepGQ R σ n (fun l y => g l (Ψ l y)) r (compC P n * C) :=
  JetRepGQ.comp' hR h0 cg cΨ hg fun b j => (hΨ b j).mono hR (Nat.sub_le n 1) le_rfl le_rfl

/-- The first-derivative entries of a family of label maps have sized jets. -/
theorem jetRepGQ_fderiv_entry {Φ : Λ → Vec 2 → Vec 2} {n r : ℕ} {P : ℝ≥0}
    (hΦ : ∀ l, Differentiable ℝ (Φ l))
    (hJ : ∀ b j, JetRepGQ R σ n (dLabelG j (fun l y => Φ l y b)) r P) (i b : Fin 2) :
    JetRepGQ R σ n (fun l y => fderiv ℝ (Φ l) y (basisVec i) b) r P :=
  (hJ b i).congr_germ fun l => Filter.Eventually.of_forall fun y =>
    fderiv_component ((hΦ l) y) b i
end

/-! **Ledger, sized jets of label coefficient arrays.** The quantitative twin of `ArrJetG`
(`Providers/GenSem/Op/ArrJet.lean`). An array of constant `c` has the entry of order `m` of size
`c · w^m`, for a fixed length scale `w > 0` (the lift length `ρ` in the applications); one label
derivative costs the factor `σ` with `σ w ≤ s` (`s` a dimensionless constant):
`ArrJetGQ R σ w n B r c`.

* `arrJetGQ_slowArr`, `arrJetGQ_iterSlow`: a slow derivative lowers the constant by `w⁻¹`,
  `c ↦ (s + 1) c w⁻¹`;
* `arrJetGQ_compArr`: the composition array has the constant `compK J n s · c₁ c₂` (the powers of
  `w` and `w⁻¹` cancel);
* `arrJetGQ_unitArr`, `arrJetGQ_smul`. -/

section
open AVRegularity.Providers.GenSem

variable {Λ : Type*} {R : (Λ → ℝ) → ℕ → ℝ≥0 → Prop} {σ w s : ℝ≥0}

variable (R σ) in
/-- Sized jets of order `n` (and `C^n` regularity) of all entries of a family of arrays: the
entry of order `m` has cost `r` and size `c w^m`. -/
def ArrJetGQ (w : ℝ≥0) (n : ℕ) (B : Λ → CArr) (r : ℕ) (c : ℝ≥0) : Prop :=
  ∀ m (α : DerivativeWord2 m),
    JetRepGQ R σ n (fun l y => B l m α y 0) r (c * w ^ m) ∧
      ∀ l, ContDiff ℝ n (fun y => B l m α y 0)

theorem ArrJetGQ.mono (hR : RepAlgQ R) {n n' : ℕ} (hn : n' ≤ n) {B : Λ → CArr} {r r' : ℕ}
    {c c' : ℝ≥0} (hB : ArrJetGQ R σ w n B r c) (hr : r ≤ r') (hc : c ≤ c') :
    ArrJetGQ R σ w n' B r' c' :=
  fun m α => ⟨(hB m α).1.mono hR hn hr (mul_le_mul' hc le_rfl),
    fun l => ((hB m α).2 l).of_le (by exact_mod_cast hn)⟩

theorem pow_mul_inv_pow (hw : w ≠ 0) (m : ℕ) : w ^ m * w⁻¹ ^ m = 1 := by
  rw [← mul_pow, mul_inv_cancel₀ hw, one_pow]

theorem sigma_le_of_mul (hw : w ≠ 0) (hσ : σ * w ≤ s) : σ ≤ s * w⁻¹ := by
  calc σ = σ * w * w⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hw, mul_one]
    _ ≤ s * w⁻¹ := mul_le_mul' hσ le_rfl

/-- **The slow derivative of an array.** -/
theorem arrJetGQ_slowArr (hR : RepAlgQ R) (hw : w ≠ 0) (hσ : σ * w ≤ s) {n : ℕ} {B : Λ → CArr}
    {r : ℕ} {c : ℝ≥0} (j : Fin 2) (hB : ArrJetGQ R σ w (n + 1) B r c) :
    ArrJetGQ R σ w n (fun l => slowArr j (B l)) (r + 1) ((s + 1) * c * w⁻¹) := by
  intro m β
  have hd : JetRepGQ R σ n (dLabelG j (fun l y => B l m β y 0)) (r + 1) (σ * (c * w ^ m)) :=
    (hB m β).1.2 j
  have hcd : ∀ l, ContDiff ℝ n (fun y => fderiv ℝ (fun X' => B l m β X' 0) y (basisVec j)) :=
    fun l => contDiff_dirDeriv_nat ((hB m β).2 l) j
  have hσ' := sigma_le_of_mul hw hσ
  cases m with
  | zero =>
    have hle : σ * (c * w ^ 0) ≤ (s + 1) * c * w⁻¹ * w ^ 0 := by
      rw [pow_zero, mul_one, mul_one]
      calc σ * c ≤ s * w⁻¹ * c := mul_le_mul' hσ' le_rfl
        _ ≤ (s + 1) * w⁻¹ * c := mul_le_mul' (mul_le_mul' le_self_add le_rfl) le_rfl
        _ = (s + 1) * c * w⁻¹ := by ring
    refine ⟨(hd.mono hR le_rfl le_rfl hle).congr_germ fun l =>
      Filter.Eventually.of_forall fun y => ?_, fun l => ?_⟩
    · simp [dLabelG, slowArr, slowExtra, slowPartial]
    · simpa [slowArr, slowExtra, dLabelG, slowPartial] using hcd l
  | succ m =>
    have hww : w⁻¹ * w ^ (m + 1) = w ^ m := by
      rw [pow_succ, ← mul_assoc, mul_comm w⁻¹, mul_assoc, inv_mul_cancel₀ hw, mul_one]
    have hmain : σ * (c * w ^ (m + 1)) ≤ s * c * w ^ m := by
      calc σ * (c * w ^ (m + 1)) = σ * w * (c * w ^ m) := by rw [pow_succ]; ring
        _ ≤ s * (c * w ^ m) := mul_le_mul' hσ le_rfl
        _ = s * c * w ^ m := by ring
    have htgt : (s + 1) * c * w⁻¹ * w ^ (m + 1) = s * c * w ^ m + c * w ^ m := by
      rw [mul_assoc ((s + 1) * c), hww]
      ring
    by_cases hj : β (Fin.last m) = j
    · have hr : JetRepGQ R σ n (fun l y => B l m (Fin.init β) y 0) (r + 1) (c * w ^ m) :=
        (hB m (Fin.init β)).1.mono hR (Nat.le_succ n) (Nat.le_succ r) le_rfl
      have hrc : ∀ l, ContDiff ℝ n (fun y => B l m (Fin.init β) y 0) := fun l =>
        ((hB m (Fin.init β)).2 l).of_le (by exact_mod_cast Nat.le_succ n)
      have hsum := JetRepGQ.add hR hcd hrc hd hr
      refine ⟨(hsum.mono hR le_rfl le_rfl ?_).congr_germ fun l =>
        Filter.Eventually.of_forall fun y => ?_, fun l => ?_⟩
      · rw [htgt]
        exact add_le_add hmain le_rfl
      · simp [slowArr, slowExtra, slowPartial, hj]
      · have := (hcd l).add (hrc l)
        simpa [slowArr, slowExtra, slowPartial, hj, dLabelG] using this
    · refine ⟨(hd.mono hR le_rfl le_rfl ?_).congr_germ fun l =>
        Filter.Eventually.of_forall fun y => ?_, fun l => ?_⟩
      · rw [htgt]
        exact hmain.trans le_self_add
      · simp [dLabelG, slowArr, slowExtra, slowPartial, hj]
      · simpa [slowArr, slowExtra, slowPartial, hj] using hcd l

/-- **Iterated slow derivatives of an array.** -/
theorem arrJetGQ_iterSlow (hR : RepAlgQ R) (hw : w ≠ 0) (hσ : σ * w ≤ s) {n : ℕ} :
    ∀ {k : ℕ} (α : DerivativeWord2 k) {B : Λ → CArr} {r : ℕ} {c : ℝ≥0},
      ArrJetGQ R σ w (n + k) B r c →
      ArrJetGQ R σ w n (fun l => iterSlow k α (B l)) (r + k) (((s + 1) * w⁻¹) ^ k * c)
  | 0, _, B, r, c, h => by
      have e : ((s + 1) * w⁻¹) ^ 0 * c = c := by simp
      show ArrJetGQ R σ w n B (r + 0) (((s + 1) * w⁻¹) ^ 0 * c)
      rw [e]
      exact h
  | k + 1, α, B, r, c, h => by
      have h1 : ArrJetGQ R σ w (n + k) (fun l => slowArr (α 0) (B l)) (r + 1)
          ((s + 1) * c * w⁻¹) :=
        arrJetGQ_slowArr hR hw hσ (α 0) (by simpa [add_assoc, add_comm 1 k] using h)
      have h2 := arrJetGQ_iterSlow hR hw hσ (fun i => α i.succ) h1
      refine h2.mono hR le_rfl (by omega) (le_of_eq ?_)
      ring

/-- The constant of the composition array. -/
def compK (J n : ℕ) (s : ℝ≥0) : ℝ≥0 := ∑ m ∈ Finset.range (J + 1), 2 ^ m * (2 ^ n * (s + 1) ^ m)

/-- **Sized jets of the composition array.** -/
theorem arrJetGQ_compArr (hR : RepAlgQ R) (hw : w ≠ 0) (hσ : σ * w ≤ s) {n : ℕ} (J : ℕ)
    {C B : Λ → CArr} {r : ℕ} {c₁ c₂ : ℝ≥0} (hC : ArrJetGQ R σ w n C r c₁)
    (hB : ArrJetGQ R σ w (n + J) B r c₂) :
    ArrJetGQ R σ w n (fun l => compArr J (C l) (B l) 0) (r + J) (compK J n s * (c₁ * c₂)) := by
  intro m' β
  have hit : ∀ m ∈ Finset.range (J + 1), ∀ α : DerivativeWord2 m,
      ArrJetGQ R σ w n (fun l => iterSlow m α (B l)) (r + J) (((s + 1) * w⁻¹) ^ m * c₂) :=
    fun m hm α => (arrJetGQ_iterSlow hR hw hσ α
      (hB.mono hR (by simp at hm; omega) le_rfl le_rfl)).mono hR le_rfl
      (by simp at hm; omega) le_rfl
  have hterm : ∀ m ∈ Finset.range (J + 1), ∀ α : DerivativeWord2 m,
      JetRepGQ R σ n (fun l y => C l m α y 0 * iterSlow m α (B l) m' β y 0) (r + J)
        (2 ^ n * (c₁ * w ^ m * (((s + 1) * w⁻¹) ^ m * c₂ * w ^ m'))) := fun m hm α =>
    JetRepGQ.mul hR ((hC m α).2) ((hit m hm α m' β).2)
      ((hC m α).1.mono hR le_rfl (by omega) le_rfl) (hit m hm α m' β).1
  have hsm : ∀ m ∈ Finset.range (J + 1), ∀ α : DerivativeWord2 m, ∀ l,
      ContDiff ℝ n (fun y => C l m α y 0 * iterSlow m α (B l) m' β y 0) := fun m hm α l =>
    ((hC m α).2 l).mul ((hit m hm α m' β).2 l)
  have hsize : ∑ m ∈ Finset.range (J + 1), ∑ _α : DerivativeWord2 m,
      2 ^ n * (c₁ * w ^ m * (((s + 1) * w⁻¹) ^ m * c₂ * w ^ m')) =
      compK J n s * (c₁ * c₂) * w ^ m' := by
    unfold compK
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    have h1 := pow_mul_inv_pow hw m
    push_cast
    calc (2 : ℝ≥0) ^ m * (2 ^ n * (c₁ * w ^ m * (((s + 1) * w⁻¹) ^ m * c₂ * w ^ m')))
        = 2 ^ m * (2 ^ n * (s + 1) ^ m) * (c₁ * c₂) * w ^ m' * (w ^ m * w⁻¹ ^ m) := by
          rw [mul_pow]
          ring
      _ = 2 ^ m * (2 ^ n * (s + 1) ^ m) * (c₁ * c₂) * w ^ m' := by rw [h1, mul_one]
  refine ⟨?_, fun l => ?_⟩
  · rw [← hsize]
    refine (JetRepGQ.finsetSum hR (n := n) (Finset.range (J + 1))
      (F := fun m l y => ∑ α : DerivativeWord2 m,
        C l m α y 0 * iterSlow m α (B l) m' β y 0)
      (fun m hm l => ContDiff.sum fun α _ => hsm m hm α l) (fun m hm => ?_)).congr_germ
      fun l => Filter.Eventually.of_forall fun y => rfl
    exact JetRepGQ.finsetSum hR Finset.univ (fun α _ l => hsm m hm α l) (fun α _ => hterm m hm α)
  · exact ContDiff.sum fun m hm => ContDiff.sum fun α _ => hsm m hm α l

theorem arrJetGQ_unitArr (hR : RepAlgQ R) (n r : ℕ) :
    ArrJetGQ R σ w n (fun _ : Λ => unitArr) r 1 := by
  intro m α
  cases m with
  | zero =>
    refine ⟨?_, fun _ => contDiff_const⟩
    have h1 : JetRepGQ R σ n (fun (_ : Λ) (_ : Vec 2) => (1 : ℝ)) r 1 := by
      simpa using jetRepGQ_const (σ := σ) hR n 1 r
    rw [pow_zero, mul_one]
    exact h1
  | succ m =>
    exact ⟨(jetRepGQ_zero hR n r).mono hR le_rfl le_rfl (zero_le), fun _ => contDiff_const⟩

theorem arrJetGQ_smul (hR : RepAlgQ R) {n : ℕ} (a : ℝ) {B : Λ → CArr} {r : ℕ} {c : ℝ≥0}
    (hB : ArrJetGQ R σ w n B r c) :
    ArrJetGQ R σ w n (fun l => a • B l) r (Real.toNNReal |a| * c) := fun m α =>
  ⟨by
    have := JetRepGQ.smul hR a (hB m α).2 (hB m α).1
    rw [mul_assoc]
    exact this.congr_germ fun _ => Filter.Eventually.of_forall fun _ => rfl,
    fun l => contDiff_const.mul ((hB m α).2 l)⟩
end

/-! **Ledger, sized jets of the operator arrays.** The quantitative twins of `Op/CovJet`,
`Op/FdbJet`, `Op/ChartJet`, `Op/PushJet` and `Op/Extract`:
* `arrJetGQ_covArr`, `arrJetGQ_covArrPow`: the arrays of the covariance operator `H:D²` and of its
  iterates, with the constants `c_H` (for `|H| ≤ c_H w²`) and `covK a n s · c_H^a`;
* `arrJetGQ_fdbStep`, `arrJetGQ_fdbIter`, `arrJetGQ_fdbArr`: the Faà di Bruno arrays of a label
  map with the Jacobian bound `P`: the array of a word of length `k` has the constant
  `(q w⁻¹)^k`, `q ≥ s + 2^{n+k} P`;
* `arrJetGQ_chartArr`, `arrJetGQ_push`, `arrJetGQ_pull`: the push and the pull of an array flux
  operator by a chart pair keep the constant up to `chartK`;
* `rep_fluxCoeff_applyArrQ`: the extracted coefficient of order `d` has the size `c w^{d-1}`. -/

section
open AVRegularity.Providers.GenSem

variable {Λ : Type*} {R : (Λ → ℝ) → ℕ → ℝ≥0 → Prop} {σ w s : ℝ≥0}

/-! ### The covariance operator -/

theorem arrJetGQ_covArr (hR : RepAlgQ R) {H : Λ → Matrix (Fin 2) (Fin 2) ℝ} {r : ℕ} {cH : ℝ≥0}
    (hH : ∀ i j, R (fun l => H l i j) r (cH * w ^ 2)) (n : ℕ) :
    ArrJetGQ R σ w n (fun l => covArr (H l)) r cH := by
  intro m α
  match m with
  | 0 => exact ⟨(jetRepGQ_zero hR n r).mono hR le_rfl le_rfl (zero_le), fun _ => contDiff_const⟩
  | 1 => exact ⟨(jetRepGQ_zero hR n r).mono hR le_rfl le_rfl (zero_le), fun _ => contDiff_const⟩
  | 2 => exact ⟨jetRepGQ_labelConst hR (hH (α 1) (α 0)) n, fun _ => contDiff_const⟩
  | m + 3 =>
    exact ⟨(jetRepGQ_zero hR n r).mono hR le_rfl le_rfl (zero_le), fun _ => contDiff_const⟩

/-- The constant of the `a`-th iterate of the covariance operator. -/
def covK : ℕ → ℕ → ℝ≥0 → ℝ≥0
  | 0, _, _ => 1
  | a + 1, n, s => compK 2 n s * covK a (n + 2) s

theorem arrJetGQ_covArrPow (hR : RepAlgQ R) (hw : w ≠ 0) (hσ : σ * w ≤ s)
    {H : Λ → Matrix (Fin 2) (Fin 2) ℝ} {r : ℕ} {cH : ℝ≥0}
    (hH : ∀ i j, R (fun l => H l i j) r (cH * w ^ 2)) :
    ∀ (a n : ℕ), ArrJetGQ R σ w n (fun l => covArrPow (H l) a) (r + 2 * a) (covK a n s * cH ^ a)
  | 0, n => by
      have h := arrJetGQ_unitArr (Λ := Λ) (σ := σ) (w := w) hR n r
      have e : covK 0 n s * cH ^ 0 = 1 := by simp [covK]
      show ArrJetGQ R σ w n (fun _ : Λ => unitArr) (r + 2 * 0) (covK 0 n s * cH ^ 0)
      rw [e]
      exact h
  | a + 1, n => by
      have h1 := arrJetGQ_covArr (σ := σ) hR hH n
      have h2 := arrJetGQ_covArrPow hR hw hσ hH a (n + 2)
      have h3 := arrJetGQ_compArr hR hw hσ 2
        (h1.mono hR le_rfl (by omega : r ≤ r + 2 * a) le_rfl) h2
      refine ArrJetGQ.mono hR le_rfl h3 (by omega) (le_of_eq ?_)
      simp only [covK]
      ring

/-! ### Faà di Bruno arrays -/

theorem arrJetGQ_fdbStep (hR : RepAlgQ R) (hw : w ≠ 0) (hσ : σ * w ≤ s) {n : ℕ} {A : Λ → CArr}
    {Φ : Λ → Vec 2 → Vec 2} {r : ℕ} {c P q : ℝ≥0} (hΦ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Φ l))
    (hJ : ∀ b j, JetRepGQ R σ n (dLabelG j (fun l y => Φ l y b)) (r + 1) P)
    (hq : s + 2 ^ n * P ≤ q) (i : Fin 2) (hA : ArrJetGQ R σ w (n + 1) A r c) :
    ArrJetGQ R σ w n (fun l => fdbStep (Φ l) i (A l)) (r + 1) (q * c * w⁻¹) := by
  intro m β
  have hd : JetRepGQ R σ n (dLabelG i (fun l y => A l m β y 0)) (r + 1) (σ * (c * w ^ m)) :=
    (hA m β).1.2 i
  have hcd : ∀ l, ContDiff ℝ n (fun y => fderiv ℝ (fun X' => A l m β X' 0) y (basisVec i)) :=
    fun l => contDiff_dirDeriv_nat ((hA m β).2 l) i
  have hσ' := sigma_le_of_mul hw hσ
  have hsq : s ≤ q := le_self_add.trans hq
  cases m with
  | zero =>
    have hle : σ * (c * w ^ 0) ≤ q * c * w⁻¹ * w ^ 0 := by
      rw [pow_zero, mul_one, mul_one]
      calc σ * c ≤ s * w⁻¹ * c := mul_le_mul' hσ' le_rfl
        _ ≤ q * w⁻¹ * c := mul_le_mul' (mul_le_mul' hsq le_rfl) le_rfl
        _ = q * c * w⁻¹ := by ring
    refine ⟨(hd.mono hR le_rfl le_rfl hle).congr_germ fun l =>
      Filter.Eventually.of_forall fun y => ?_, fun l => ?_⟩
    · simp [fdbStep, fdbExtra, slowPartial, dLabelG]
    · simpa [fdbStep, fdbExtra, slowPartial] using hcd l
  | succ m =>
    have hww : w⁻¹ * w ^ (m + 1) = w ^ m := by
      rw [pow_succ, ← mul_assoc, mul_comm w⁻¹, mul_assoc, inv_mul_cancel₀ hw, mul_one]
    have hmain : σ * (c * w ^ (m + 1)) ≤ s * c * w ^ m := by
      calc σ * (c * w ^ (m + 1)) = σ * w * (c * w ^ m) := by rw [pow_succ]; ring
        _ ≤ s * (c * w ^ m) := mul_le_mul' hσ le_rfl
        _ = s * c * w ^ m := by ring
    have hr : JetRepGQ R σ n (fun l y => A l m (Fin.init β) y 0) (r + 1) (c * w ^ m) :=
      (hA m (Fin.init β)).1.mono hR (Nat.le_succ n) (Nat.le_succ r) le_rfl
    have hrc : ∀ l, ContDiff ℝ n (fun y => A l m (Fin.init β) y 0) := fun l =>
      ((hA m (Fin.init β)).2 l).of_le (by exact_mod_cast Nat.le_succ n)
    have hm := JetRepGQ.mul hR hrc
      (fun l => contDiff_fderiv_entry (hΦ l) n i (β (Fin.last m))) hr
      (jetRepGQ_fderiv_entry (fun l => (hΦ l).differentiable (by simp)) hJ i (β (Fin.last m)))
    have hsum := JetRepGQ.add hR hcd (fun l => (hrc l).mul
      (contDiff_fderiv_entry (hΦ l) n i (β (Fin.last m)))) hd hm
    have hle : σ * (c * w ^ (m + 1)) + 2 ^ n * (c * w ^ m * P) ≤ q * c * w⁻¹ * w ^ (m + 1) := by
      rw [mul_assoc (q * c), hww]
      calc σ * (c * w ^ (m + 1)) + 2 ^ n * (c * w ^ m * P)
          ≤ s * c * w ^ m + 2 ^ n * (c * w ^ m * P) := add_le_add hmain le_rfl
        _ = (s + 2 ^ n * P) * (c * w ^ m) := by ring
        _ ≤ q * (c * w ^ m) := mul_le_mul' hq le_rfl
        _ = q * c * w ^ m := by ring
    refine ⟨(hsum.mono hR le_rfl le_rfl hle).congr_germ fun l =>
      Filter.Eventually.of_forall fun y => ?_, fun l => ?_⟩
    · simp [fdbStep, fdbExtra, slowPartial]
    · simpa [fdbStep, fdbExtra, slowPartial] using
        (hcd l).add ((hrc l).mul (contDiff_fderiv_entry (hΦ l) n i (β (Fin.last m))))

theorem arrJetGQ_fdbIter (hR : RepAlgQ R) (hw : w ≠ 0) (hσ : σ * w ≤ s) {n : ℕ}
    {Φ : Λ → Vec 2 → Vec 2} {P q : ℝ≥0} (hΦ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Φ l)) :
    ∀ {k : ℕ} (α : DerivativeWord2 k) {A : Λ → CArr} {r : ℕ} {c : ℝ≥0},
      (∀ b j, JetRepGQ R σ (n + k) (dLabelG j (fun l y => Φ l y b)) (r + 1) P) →
      s + 2 ^ (n + k) * P ≤ q → ArrJetGQ R σ w (n + k) A r c →
      ArrJetGQ R σ w n (fun l => fdbIter (Φ l) k α (A l)) (r + k) ((q * w⁻¹) ^ k * c)
  | 0, _, A, r, c, _, _, h => by
      have e : (q * w⁻¹) ^ 0 * c = c := by simp
      show ArrJetGQ R σ w n A (r + 0) ((q * w⁻¹) ^ 0 * c)
      rw [e]
      exact h
  | k + 1, α, A, r, c, hJ, hq, h => by
      have hq' : s + 2 ^ (n + k) * P ≤ q :=
        le_trans (add_le_add le_rfl (mul_le_mul'
          (pow_le_pow_right₀ one_le_two (by omega)) le_rfl)) hq
      have h1 : ArrJetGQ R σ w (n + k) (fun l => fdbStep (Φ l) (α 0) (A l)) (r + 1)
          (q * c * w⁻¹) :=
        arrJetGQ_fdbStep hR hw hσ hΦ (fun b j => (hJ b j).mono hR (by omega) le_rfl le_rfl) hq'
          (α 0) (by simpa [add_assoc, add_comm 1 k] using h)
      have h2 := arrJetGQ_fdbIter hR hw hσ hΦ (fun i => α i.succ)
        (fun b j => (hJ b j).mono hR (by omega) (by omega) le_rfl) hq' h1
      refine ArrJetGQ.mono hR le_rfl h2 (by omega) (le_of_eq ?_)
      ring

/-- **Sized jets of the Faà di Bruno array** of a word of length `k`. -/
theorem arrJetGQ_fdbArr (hR : RepAlgQ R) (hw : w ≠ 0) (hσ : σ * w ≤ s) {n k : ℕ}
    {Φ : Λ → Vec 2 → Vec 2} {r : ℕ} {P q : ℝ≥0} (hΦ : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Φ l))
    (hJ : ∀ b j, JetRepGQ R σ (n + k) (dLabelG j (fun l y => Φ l y b)) (r + 1) P)
    (hq : s + 2 ^ (n + k) * P ≤ q) (α : DerivativeWord2 k) :
    ArrJetGQ R σ w n (fun l => fdbArr (Φ l) α) (r + k) ((q * w⁻¹) ^ k) := by
  have h := arrJetGQ_fdbIter hR hw hσ hΦ α hJ hq (arrJetGQ_unitArr hR (n + k) r)
  rwa [mul_one] at h

/-! ### Charts -/

/-- The constant of the chart transformation of an array of order `K`. -/
def chartK (n K : ℕ) (PN q : ℝ≥0) : ℝ≥0 :=
  2 * (2 ^ n * ∑ m ∈ Finset.range (K + 1), 2 ^ m * (2 ^ n * (compC PN n ^ 2 * q ^ m)))

/-- **Sized jets of the transformed array.** -/
theorem arrJetGQ_chartArr (hR : RepAlgQ R) (hw : w ≠ 0) (hσ : σ * w ≤ s) {n K : ℕ}
    {M : Λ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {N Ψ : Λ → Vec 2 → Vec 2} {A : Λ → Fin 2 → CArr}
    {r : ℕ} {PN PΨ q cM cA : ℝ≥0}
    (hN0 : ∀ l, N l 0 = 0) (hNs : ∀ l, ContDiff ℝ n (N l))
    (hNj : ∀ b j, JetRepGQ R σ n (dLabelG j (fun l y => N l y b)) (r + 1) PN)
    (hΨs : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Ψ l))
    (hΨj : ∀ b j, JetRepGQ R σ (n + K) (dLabelG j (fun l y => Ψ l y b)) (r + 1) PΨ)
    (hq : s + 2 ^ (n + K) * PΨ ≤ q)
    (hMj : ∀ c k, JetRepGQ R σ n (fun l p => M l p c k) r cM)
    (hMs : ∀ c k l, ContDiff ℝ n (fun p => M l p c k))
    (hA : ∀ k, ArrJetGQ R σ w n (fun l => A l k) r cA) (c : Fin 2) :
    ArrJetGQ R σ w n (fun l => chartArr (M l) (N l) (Ψ l) K (A l) c) (r + K)
      (chartK n K PN q * (cM * cA)) := by
  intro m' γ
  have hAc : ∀ k m (α : DerivativeWord2 m),
      JetRepGQ R σ n (fun l y => A l k m α (N l y) 0) (r + K) (compC PN n * (cA * w ^ m)) :=
    fun k m α => (JetRepGQ.comp hR hN0 (fun l => (hA k m α).2 l) hNs (hA k m α).1 hNj).mono hR
      le_rfl (by omega) le_rfl
  have hAs : ∀ k m (α : DerivativeWord2 m) l, ContDiff ℝ n (fun y => A l k m α (N l y) 0) :=
    fun k m α l => ((hA k m α).2 l).comp (hNs l)
  have hFc : ∀ m ∈ Finset.range (K + 1), ∀ (α : DerivativeWord2 m),
      JetRepGQ R σ n (fun l y => fdbArr (Ψ l) α m' γ (N l y) 0) (r + K)
        (compC PN n * ((q * w⁻¹) ^ m * w ^ m')) := by
    intro m hm α
    have hmK : m ≤ K := by simpa [Nat.lt_succ_iff] using hm
    have hqm : s + 2 ^ (n + m) * PΨ ≤ q :=
      le_trans (add_le_add le_rfl (mul_le_mul'
        (pow_le_pow_right₀ one_le_two (by omega)) le_rfl)) hq
    have hF := arrJetGQ_fdbArr hR hw hσ (n := n) (k := m) hΨs
      (fun b j => (hΨj b j).mono hR (by omega) le_rfl le_rfl) hqm α m' γ
    exact (JetRepGQ.comp hR hN0 (fun l => hF.2 l) hNs hF.1
      (fun b j => (hNj b j).mono hR le_rfl (by omega) le_rfl)).mono hR le_rfl (by omega) le_rfl
  have hFs : ∀ m (α : DerivativeWord2 m) l,
      ContDiff ℝ n (fun y => fdbArr (Ψ l) α m' γ (N l y) 0) := by
    intro m α l
    have := arrSlowSmooth_fdbArr (hΨs l) n α m' γ 0
    exact this.comp (hNs l)
  have hterm : ∀ k, ∀ m ∈ Finset.range (K + 1), ∀ α : DerivativeWord2 m,
      JetRepGQ R σ n (fun l y => A l k m α (N l y) 0 * fdbArr (Ψ l) α m' γ (N l y) 0) (r + K)
        (2 ^ n * (compC PN n * (cA * w ^ m) * (compC PN n * ((q * w⁻¹) ^ m * w ^ m')))) :=
    fun k m hm α => JetRepGQ.mul hR (hAs k m α) (hFs m α) (hAc k m α) (hFc m hm α)
  have hts : ∀ k m (α : DerivativeWord2 m) l,
      ContDiff ℝ n (fun y => A l k m α (N l y) 0 * fdbArr (Ψ l) α m' γ (N l y) 0) :=
    fun k m α l => (hAs k m α l).mul (hFs m α l)
  have hinner : ∀ k, JetRepGQ R σ n (fun l y => ∑ m ∈ Finset.range (K + 1),
      ∑ α : DerivativeWord2 m, A l k m α (N l y) 0 * fdbArr (Ψ l) α m' γ (N l y) 0) (r + K)
      (∑ m ∈ Finset.range (K + 1), ∑ _α : DerivativeWord2 m,
        2 ^ n * (compC PN n * (cA * w ^ m) * (compC PN n * ((q * w⁻¹) ^ m * w ^ m')))) :=
    fun k => JetRepGQ.finsetSum hR _ (fun m _ l => ContDiff.sum fun α _ => hts k m α l)
      fun m hm => JetRepGQ.finsetSum hR _ (fun α _ l => hts k m α l) fun α _ => hterm k m hm α
  have hins : ∀ k l, ContDiff ℝ n (fun y => ∑ m ∈ Finset.range (K + 1),
      ∑ α : DerivativeWord2 m, A l k m α (N l y) 0 * fdbArr (Ψ l) α m' γ (N l y) 0) := fun k l =>
    ContDiff.sum fun m _ => ContDiff.sum fun α _ => hts k m α l
  have hinnerSize : ∑ m ∈ Finset.range (K + 1), ∑ _α : DerivativeWord2 m,
      2 ^ n * (compC PN n * (cA * w ^ m) * (compC PN n * ((q * w⁻¹) ^ m * w ^ m'))) =
      (∑ m ∈ Finset.range (K + 1), 2 ^ m * (2 ^ n * (compC PN n ^ 2 * q ^ m))) * cA * w ^ m' := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    have h1 := pow_mul_inv_pow hw m
    push_cast
    calc (2 : ℝ≥0) ^ m *
          (2 ^ n * (compC PN n * (cA * w ^ m) * (compC PN n * ((q * w⁻¹) ^ m * w ^ m'))))
        = 2 ^ m * (2 ^ n * (compC PN n ^ 2 * q ^ m)) * cA * w ^ m' * (w ^ m * w⁻¹ ^ m) := by
          rw [mul_pow]
          ring
      _ = 2 ^ m * (2 ^ n * (compC PN n ^ 2 * q ^ m)) * cA * w ^ m' := by rw [h1, mul_one]
  have hsize : ∑ _k : Fin 2, 2 ^ n * (cM *
      ∑ m ∈ Finset.range (K + 1), ∑ _α : DerivativeWord2 m,
        2 ^ n * (compC PN n * (cA * w ^ m) * (compC PN n * ((q * w⁻¹) ^ m * w ^ m')))) =
      chartK n K PN q * (cM * cA) * w ^ m' := by
    rw [hinnerSize, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold chartK
    push_cast
    ring
  refine ⟨?_, fun l => ?_⟩
  · rw [← hsize]
    refine (JetRepGQ.finsetSum hR (n := n) Finset.univ
      (F := fun k l y => M l y c k * ∑ m ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 m,
        A l k m α (N l y) 0 * fdbArr (Ψ l) α m' γ (N l y) 0)
      (fun k _ l => (hMs c k l).mul (hins k l)) fun k _ =>
        JetRepGQ.mul hR (hMs c k) (hins k) ((hMj c k).mono hR le_rfl (by omega) le_rfl)
          (hinner k)).congr_germ fun l =>
      Filter.Eventually.of_forall fun y => rfl
  · show ContDiff ℝ n (fun y => ∑ k : Fin 2, M l y c k * ∑ m ∈ Finset.range (K + 1),
      ∑ α : DerivativeWord2 m, A l k m α (N l y) 0 * fdbArr (Ψ l) α m' γ (N l y) 0)
    exact ContDiff.sum fun k _ => (hMs c k l).mul (hins k l)

/-- **Sized jets of the pushed array.** -/
theorem arrJetGQ_push (hR : RepAlgQ R) (hw : w ≠ 0) (hσ : σ * w ≤ s) {n K : ℕ}
    {Ψ Ψinv : Λ → Vec 2 → Vec 2} {A : Λ → Fin 2 → CArr} {r : ℕ} {PΨ PI q cA : ℝ≥0}
    (hΨs : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Ψ l))
    (hΨj : ∀ b j, JetRepGQ R σ (n + K) (dLabelG j (fun l y => Ψ l y b)) r PΨ)
    (hq : s + 2 ^ (n + K) * PΨ ≤ q)
    (hIs : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Ψinv l)) (hI0 : ∀ l, Ψinv l 0 = 0)
    (hIj : ∀ b j, JetRepGQ R σ n (dLabelG j (fun l y => Ψinv l y b)) r PI)
    (hA : ∀ k, ArrJetGQ R σ w n (fun l => A l k) r cA) (c : Fin 2) :
    ArrJetGQ R σ w n
      (fun l => chartArr (fun p => jacMatrix (Ψ l) (Ψinv l p)) (Ψinv l) (Ψ l) K (A l) c)
      (r + K) (chartK n K PI q * (compC PI n * PΨ * cA)) := by
  have hIs' : ∀ l, ContDiff ℝ n (Ψinv l) := fun l => (hIs l).of_le (by exact_mod_cast le_top)
  have hIj' : ∀ b j, JetRepGQ R σ n (dLabelG j (fun l y => Ψinv l y b)) (r + 1) PI :=
    fun b j => (hIj b j).mono hR le_rfl (by omega) le_rfl
  have hJe : ∀ c k, JetRepGQ R σ n (fun l w => jacMatrix (Ψ l) w c k) r PΨ := fun c k =>
    jetRepGQ_fderiv_entry (fun l => (hΨs l).differentiable (by simp))
      (fun b j => (hΨj b j).mono hR (by omega) le_rfl le_rfl) k c
  have hJs : ∀ c k l, ContDiff ℝ n (fun w => jacMatrix (Ψ l) w c k) := fun c k l =>
    contDiff_fderiv_entry (hΨs l) n k c
  exact arrJetGQ_chartArr hR hw hσ hI0 hIs' hIj' hΨs
    (fun b j => (hΨj b j).mono hR le_rfl (by omega) le_rfl) hq
    (fun c k => JetRepGQ.comp hR hI0 (hJs c k) hIs' (hJe c k) hIj')
    (fun c k l => (hJs c k l).comp (hIs' l)) hA c

/-- **Sized jets of the pulled array.** The entries of `(DΦ)⁻¹` are hypotheses. -/
theorem arrJetGQ_pull (hR : RepAlgQ R) (hw : w ≠ 0) (hσ : σ * w ≤ s) {n K : ℕ}
    {Φ Φinv : Λ → Vec 2 → Vec 2} {B : Λ → Fin 2 → CArr} {r : ℕ} {PΦ PI q cM cB : ℝ≥0}
    (hΦ0 : ∀ l, Φ l 0 = 0) (hΦs : ∀ l, ContDiff ℝ n (Φ l))
    (hΦj : ∀ b j, JetRepGQ R σ n (dLabelG j (fun l y => Φ l y b)) r PΦ)
    (hIs : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Φinv l))
    (hIj : ∀ b j, JetRepGQ R σ (n + K) (dLabelG j (fun l y => Φinv l y b)) r PI)
    (hq : s + 2 ^ (n + K) * PI ≤ q)
    (hMj : ∀ c k, JetRepGQ R σ n (fun l p => ((jacMatrix (Φ l) p)⁻¹) c k) r cM)
    (hMs : ∀ c k l, ContDiff ℝ n (fun p => ((jacMatrix (Φ l) p)⁻¹) c k))
    (hB : ∀ k, ArrJetGQ R σ w n (fun l => B l k) r cB) (c : Fin 2) :
    ArrJetGQ R σ w n
      (fun l => chartArr (fun p => (jacMatrix (Φ l) p)⁻¹) (Φ l) (Φinv l) K (B l) c)
      (r + K) (chartK n K PΦ q * (cM * cB)) :=
  arrJetGQ_chartArr hR hw hσ hΦ0 hΦs
    (fun b j => (hΦj b j).mono hR le_rfl (by omega) le_rfl) hIs
    (fun b j => (hIj b j).mono hR le_rfl (by omega) le_rfl) hq hMj hMs hB c

/-! ### Extraction -/

/-- **The extracted coefficient of order `d`** has the size `c w^{d-1}`. -/
theorem rep_fluxCoeff_applyArrQ (hR : RepAlgQ R) {K : ℕ} {A : Λ → Fin 2 → CArr} (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (hd : d - 1 ≤ K) (c : Fin 2) {r : ℕ} {cA : ℝ≥0}
    (hA : ∀ m (α : DerivativeWord2 m), R (fun l => A l c m α 0 0) r (cA * w ^ m)) :
    R (fun l => fluxCoeff (fun g y k => applyArr K (A l k) g y 0) d I 0 c) r
      (cA * w ^ (d - 1)) := by
  have e : (fun l => fluxCoeff (fun g y k => applyArr K (A l k) g y 0) d I 0 c) =
      fun l => (((d - 1).factorial : ℝ)⁻¹) *
        ∑ σ : Equiv.Perm (Fin (d - 1)), A l c (d - 1) (I ∘ σ) 0 0 :=
    funext fun l => fluxCoeff_applyArr K (A l) d I hd c
  rw [e]
  have h := hR.smul (hR.finsetSum (Finset.univ : Finset (Equiv.Perm (Fin (d - 1))))
    (F := fun σ l => A l c (d - 1) (I ∘ σ) 0 0) (C := fun _ => cA * w ^ (d - 1))
    fun σ _ => hA _ _) (((d - 1).factorial : ℝ)⁻¹)
  refine hR.mono h le_rfl (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hf : (((d - 1).factorial : ℕ) : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (d - 1)).ne'
  have h1 : Real.toNNReal |(((d - 1).factorial : ℕ) : ℝ)⁻¹| = (((d - 1).factorial : ℕ) : ℝ≥0)⁻¹ := by
    rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)), Real.toNNReal_inv,
      Real.toNNReal_natCast]
  rw [h1, ← mul_assoc, inv_mul_cancel₀ hf, one_mul]
end

end AVRegularity.Providers.CascadeInvariants
end
