-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.CascadeInvariants.Jet.Ops
public import AVRegularity.Proofs.GenSem.First.Identity

/-! **Ledger, first source: closure of the sized arrays.** Generic facts of the sized jet calculus
used by the first-source chain, for any sized algebra `R`:
* `JetRepGQ.of_ordered`: sized jets from sized ordered derivatives (the converse of
  `JetRepGQ.orderedDerivative`);
* `JetRepGQ.comap`, `ArrJetGQ.comap`: reindexing along a map of the indices;
* `ArrJetGQ.add`, `ArrJetGQ.sum`, `ArrJetGQ.neg`, `arrJetGQ_zero`: sums add the constants;
* `arrJetGQ_matGradArr`: the order-one array of `M ∇`, with the constant `c` for entries of size
  `c w`;
* `arrJetGQ_polyArr`: the covariance polynomial `∑_{l ≤ p} w_l 𝒞^l`, with the constant
  `polyK p w_l n s c_H`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev Filter Topology
open scoped NNReal

namespace AVRegularity.Providers.CascadeInvariants

open AVRegularity.Providers.GenSem

variable {Λ : Type*} {R : (Λ → ℝ) → ℕ → ℝ≥0 → Prop} {σ w s : ℝ≥0}

/-- **Sized jets from sized ordered derivatives.** -/
theorem JetRepGQ.of_ordered (hR : RepAlgQ R) : ∀ {n : ℕ} {g : Λ → Vec 2 → ℝ} {r : ℕ} {C : ℝ≥0},
    (∀ m, m ≤ n → ∀ β : DerivativeWord2 m,
      R (fun l => AVRegularity.orderedDerivative β (g l) 0) (r + m) (σ ^ m * C)) →
    JetRepGQ R σ n g r C
  | 0, g, r, C, h => by
      have h0 := h 0 le_rfl Fin.elim0
      simp only [orderedDerivative_zero_word, pow_zero, one_mul, add_zero] at h0
      exact h0
  | n + 1, g, r, C, h => by
      have h0 := h 0 (Nat.zero_le _) Fin.elim0
      simp only [orderedDerivative_zero_word, pow_zero, one_mul, add_zero] at h0
      refine ⟨h0, fun j => JetRepGQ.of_ordered hR fun m hm β => ?_⟩
      have h1 := h (m + 1) (by omega) (Fin.cons j β)
      have e : (fun l => AVRegularity.orderedDerivative (Fin.cons j β : DerivativeWord2 (m + 1))
          (g l) 0) = fun l => AVRegularity.orderedDerivative β (dLabelG j g l) 0 := by
        funext l
        rw [orderedDerivative_succ]
        rfl
      rw [e] at h1
      refine hR.mono h1 (by omega) (le_of_eq ?_)
      ring

section comap

variable {Λ' : Type*} {R' : (Λ' → ℝ) → ℕ → ℝ≥0 → Prop}

/-- Sized jets reindex along a map of the indices. -/
theorem JetRepGQ.comap (f : Λ' → Λ) (hf : ∀ F r C, R F r C → R' (fun l' => F (f l')) r C) :
    ∀ {n : ℕ} {g : Λ → Vec 2 → ℝ} {r : ℕ} {C : ℝ≥0}, JetRepGQ R σ n g r C →
      JetRepGQ R' σ n (fun l' => g (f l')) r C
  | 0, _, _, _, hg => hf _ _ _ hg
  | _ + 1, _, _, _, hg => ⟨hf _ _ _ hg.1, fun j => JetRepGQ.comap f hf (hg.2 j)⟩

theorem ArrJetGQ.comap (f : Λ' → Λ) (hf : ∀ F r C, R F r C → R' (fun l' => F (f l')) r C)
    {n : ℕ} {B : Λ → CArr} {r : ℕ} {c : ℝ≥0} (hB : ArrJetGQ R σ w n B r c) :
    ArrJetGQ R' σ w n (fun l' => B (f l')) r c := fun m α =>
  ⟨JetRepGQ.comap f hf (hB m α).1, fun l' => (hB m α).2 (f l')⟩

end comap

/-! ### Sums -/

theorem arrJetGQ_zero (hR : RepAlgQ R) (n r : ℕ) :
    ArrJetGQ R σ w n (fun _ : Λ => (0 : CArr)) r 0 := fun _ _ =>
  ⟨((jetRepGQ_zero hR n r).mono hR le_rfl le_rfl (zero_le)).congr_germ fun _ =>
      Filter.Eventually.of_forall fun _ => rfl,
    fun _ => contDiff_const⟩

theorem ArrJetGQ.add (hR : RepAlgQ R) {n : ℕ} {A B : Λ → CArr} {r : ℕ} {c₁ c₂ : ℝ≥0}
    (hA : ArrJetGQ R σ w n A r c₁) (hB : ArrJetGQ R σ w n B r c₂) :
    ArrJetGQ R σ w n (fun l => A l + B l) r (c₁ + c₂) := fun m α =>
  ⟨by
    rw [add_mul]
    exact (JetRepGQ.add hR (hA m α).2 (hB m α).2 (hA m α).1 (hB m α).1).congr_germ fun _ =>
      Filter.Eventually.of_forall fun _ => rfl,
    fun l => ((hA m α).2 l).add ((hB m α).2 l)⟩

theorem ArrJetGQ.sum (hR : RepAlgQ R) {n : ℕ} {κ : Type*} (S : Finset κ) {A : κ → Λ → CArr}
    {r : ℕ} {c : κ → ℝ≥0} (hA : ∀ k ∈ S, ArrJetGQ R σ w n (A k) r (c k)) :
    ArrJetGQ R σ w n (fun l => ∑ k ∈ S, A k l) r (∑ k ∈ S, c k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using arrJetGQ_zero (σ := σ) (w := w) hR n r
  | insert a S ha ih =>
    have := ArrJetGQ.add hR (hA a (Finset.mem_insert_self a S))
      (ih fun k hk => hA k (Finset.mem_insert_of_mem hk))
    simpa [Finset.sum_insert ha] using this

theorem ArrJetGQ.neg (hR : RepAlgQ R) {n : ℕ} {B : Λ → CArr} {r : ℕ} {c : ℝ≥0}
    (hB : ArrJetGQ R σ w n B r c) : ArrJetGQ R σ w n (fun l => -B l) r c := by
  have h := arrJetGQ_smul hR (-1) hB
  simp only [abs_neg, abs_one, Real.toNNReal_one, one_mul, neg_smul, one_smul] at h
  exact h

/-! ### Matrix times gradient -/

/-- **The order-one array of `M ∇`**: entries of size `c w` give the constant `c`. -/
theorem arrJetGQ_matGradArr (hR : RepAlgQ R) {n : ℕ} {M : Λ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {r : ℕ} {c : ℝ≥0} (hMj : ∀ a b, JetRepGQ R σ n (fun l x => M l x a b) r (c * w))
    (hMs : ∀ a b l, ContDiff ℝ n (fun x => M l x a b)) (e : Fin 2) :
    ArrJetGQ R σ w n (fun l => matGradArr (M l) e) r c := by
  intro m α
  match m with
  | 0 =>
    exact ⟨((jetRepGQ_zero hR n r).mono hR le_rfl le_rfl (zero_le)).congr_germ fun _ =>
      Filter.Eventually.of_forall fun _ => rfl, fun _ => contDiff_const⟩
  | 1 =>
    refine ⟨?_, fun l => hMs e (α 0) l⟩
    rw [pow_one]
    exact hMj e (α 0)
  | m + 2 =>
    exact ⟨((jetRepGQ_zero hR n r).mono hR le_rfl le_rfl (zero_le)).congr_germ fun _ =>
      Filter.Eventually.of_forall fun _ => rfl, fun _ => contDiff_const⟩

/-! ### Covariance polynomials -/

/-- The constant of the covariance polynomial with the weights `wt`. -/
def polyK (p : ℕ) (wt : ℕ → ℝ) (n : ℕ) (s cH : ℝ≥0) : ℝ≥0 :=
  ∑ l ∈ Finset.range (p + 1), Real.toNNReal |wt l| * (covK l n s * cH ^ l)

/-- **Sized jets of a covariance polynomial.** -/
theorem arrJetGQ_polyArr (hR : RepAlgQ R) (hw : w ≠ 0) (hσ : σ * w ≤ s)
    {H : Λ → Matrix (Fin 2) (Fin 2) ℝ} {r : ℕ} {cH : ℝ≥0}
    (hH : ∀ i j, R (fun l => H l i j) r (cH * w ^ 2)) (p : ℕ) (wt : ℕ → ℝ) (n : ℕ) :
    ArrJetGQ R σ w n (fun l => polyArr (H l) p wt) (r + 2 * p) (polyK p wt n s cH) := by
  unfold polyArr polyK
  refine ArrJetGQ.sum hR _ fun l hl => ?_
  have hlp : l ≤ p := by simpa [Nat.lt_succ_iff] using hl
  exact arrJetGQ_smul hR (wt l) ((arrJetGQ_covArrPow hR hw hσ hH l n).mono hR le_rfl
    (by omega) le_rfl)

end AVRegularity.Providers.CascadeInvariants
