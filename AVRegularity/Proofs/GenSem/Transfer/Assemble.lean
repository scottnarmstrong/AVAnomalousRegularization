-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.GenSem.ChainMetric
public import AVRegularity.Definitions.Construction.DiagLetter
public import AVRegularity.Statements.Construction.IsFastProfile

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **Context expressions of the transfer.** Represented context functions
(`CtxRep`): an expression scheduled, from the seed, denoting a function that agrees with a given
context function under a context condition. Closure under constants, sums (finite), products and
the evaluation at an appended child (K6); the entries of the inverse chart transition
`J⁻¹ = F_t(0)⁻¹ F^♮_t(0)` are the geometric letters `jacInv` (own frame) and `jac` (child frame). -/

variable (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports)

/-- `e` is scheduled, from the seed, and denotes a function equal to `φ` under the condition `P`. -/
def CtxRep {i : ℕ} {pc : ℤ} (P : ℝ → RealChain → Vec 2 → Prop) (φ : ℝ → RealChain → Vec 2 → ℝ)
    (e : Gen .ctx i pc) : Prop :=
  Gen.IsScheduled D e ∧ Gen.FromSeed 𝒮 e ∧ ∃ f : GenSort.Sem .ctx, Gen.Denotes D bw j₀ e f ∧
    ∀ t ch z, P t ch z → f t ch z = φ t ch z

variable {D bw j₀ 𝒮}

namespace CtxRep

variable {i : ℕ} {pc : ℤ} {P : ℝ → RealChain → Vec 2 → Prop}

theorem congr {φ ψ : ℝ → RealChain → Vec 2 → ℝ} {e : Gen .ctx i pc} (h : CtxRep D bw j₀ 𝒮 P φ e)
    (hψ : ∀ t ch z, P t ch z → φ t ch z = ψ t ch z) : CtxRep D bw j₀ 𝒮 P ψ e := by
  obtain ⟨hs, hf, f, hd, hv⟩ := h
  exact ⟨hs, hf, f, hd, fun t ch z hP => (hv t ch z hP).trans (hψ t ch z hP)⟩

theorem const (c : ℝ) :
    CtxRep D bw j₀ 𝒮 P (fun _ _ _ => c) (Gen.time (s := .ctx) (i := i) (p := pc) (.const c)) :=
  ⟨.timeConst c, .time _, _, .time _, fun _ _ _ _ => rfl⟩

theorem add {φ ψ : ℝ → RealChain → Vec 2 → ℝ} {a b : Gen .ctx i pc}
    (ha : CtxRep D bw j₀ 𝒮 P φ a) (hb : CtxRep D bw j₀ 𝒮 P ψ b) :
    CtxRep D bw j₀ 𝒮 P (fun t ch z => φ t ch z + ψ t ch z) (Gen.add a b) := by
  obtain ⟨sa, fa, f, hf, hφ⟩ := ha
  obtain ⟨sb, fb, g, hg, hψ⟩ := hb
  exact ⟨.add sa sb, .add fa fb, GenSort.add .ctx f g, .add hf hg, fun t ch z hP => by
    show f t ch z + g t ch z = _
    rw [hφ t ch z hP, hψ t ch z hP]⟩

theorem mul {φ ψ : ℝ → RealChain → Vec 2 → ℝ} {a b : Gen .ctx i pc}
    (ha : CtxRep D bw j₀ 𝒮 P φ a) (hb : CtxRep D bw j₀ 𝒮 P ψ b) :
    CtxRep D bw j₀ 𝒮 P (fun t ch z => φ t ch z * ψ t ch z) (Gen.mul a b) := by
  obtain ⟨sa, fa, f, hf, hφ⟩ := ha
  obtain ⟨sb, fb, g, hg, hψ⟩ := hb
  exact ⟨.mul sa sb, .mul fa fb, GenSort.mul .ctx f g, .mul hf hg, fun t ch z hP => by
    show f t ch z * g t ch z = _
    rw [hφ t ch z hP, hψ t ch z hP]⟩

/-- Finite sums. -/
theorem finsetSum {κ : Type*} (s : Finset κ) {φ : κ → ℝ → RealChain → Vec 2 → ℝ}
    (h : ∀ k ∈ s, ∃ e : Gen .ctx i pc, CtxRep D bw j₀ 𝒮 P (φ k) e) :
    ∃ e : Gen .ctx i pc, CtxRep D bw j₀ 𝒮 P (fun t ch z => ∑ k ∈ s, φ k t ch z) e := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨_, (const 0).congr fun _ _ _ _ => by simp⟩
  | insert a s ha ih =>
    obtain ⟨e₁, h₁⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨e₂, h₂⟩ := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    exact ⟨_, (h₁.add h₂).congr fun t ch z _ => by rw [Finset.sum_insert ha]⟩

end CtxRep

/-- **The evaluation at the appended child (K6).** A family expression whose denotation agrees with
`ψ` at the appended child, where the weight `ϖ_{i+1,k}` does not vanish, gives the context function
`ϖ_{i+1,k}(t) ψ(t, 𝒜^♮)`. -/
theorem ctxRep_evalChild {i : ℕ} {pc : ℤ} (P : ℝ → RealChain → Vec 2 → Prop) (k : ℤ)
    (hk : Odd k ∧ IsScheduledIn D i k pc) {c : Gen .fam (i + 1) k} {ψ : ℝ → RealChain → ℝ}
    (hs : Gen.IsScheduled D c) (hf : Gen.FromSeed 𝒮 c) {fc : GenSort.Sem .fam}
    (hd : Gen.Denotes D bw j₀ c fc)
    (hv : ∀ t ch z, P t ch z → ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0 →
      fc t (ch.appendChild D k t z) = ψ t (ch.appendChild D k t z)) :
    CtxRep D bw j₀ 𝒮 P (fun t ch z => ocCutoff D.α D.q D.Λ (i + 1) k t * ψ t (ch.appendChild D k t z))
      (Gen.evalChild (i := i) (p := pc) k c) := by
  refine ⟨.evalChild k hk.1 hk.2 hs, .evalChild k hf, _, .evalChild k hd, fun t ch z hP => ?_⟩
  show ocCutoff D.α D.q D.Λ (i + 1) k t * fc t (ch.appendChild D k t z) =
    ocCutoff D.α D.q D.Λ (i + 1) k t * ψ t (ch.appendChild D k t z)
  by_cases h0 : ocCutoff D.α D.q D.Λ (i + 1) k t = 0
  · rw [h0, zero_mul, zero_mul]
  · rw [hv t ch z hP h0]

/-- The expression of the entry `(a, b)` of `J⁻¹ = F_t(0)⁻¹ F^♮_t(0)` for the child of the slot `k`. -/
def kExpr (i : ℕ) (pc k : ℤ) (a b : Fin 2) : Gen .ctx i pc :=
  Gen.add (Gen.mul (Gen.geo .own (.jacInv a 0)) (Gen.geo (.child k) (.jac 0 b)))
    (Gen.mul (Gen.geo .own (.jacInv a 1)) (Gen.geo (.child k) (.jac 1 b)))

/-- The inverse chart transition at a context. -/
theorem childTransition_inv (hζ : IsFastProfile D.ζ) (k : ℤ) (t : ℝ) (ch : RealChain) (z : Vec 2) :
    (childTransition D k t ch z)⁻¹ = (ch.famJac D t)⁻¹ * (ch.appendChild D k t z).famJac D t := by
  rw [childTransition, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ (famJac_isUnit D hζ _ t)]

/-- `kExpr` denotes the entries of the inverse chart transition, at every context and every time
where the weight `ϖ_{i+1,k}` does not vanish (the child letters are gated by it). -/
theorem denotes_kExpr (hζ : IsFastProfile D.ζ) (i : ℕ) (pc k : ℤ) (a b : Fin 2) :
    ∃ f : GenSort.Sem .ctx, Gen.Denotes D bw j₀ (kExpr i pc k a b) f ∧
      ∀ t, ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0 → ∀ ch z,
        f t ch z = (childTransition D k t ch z)⁻¹ a b := by
  refine ⟨_, .add (.mul (.geo _ _) (.geo _ _)) (.mul (.geo _ _) (.geo _ _)), fun t ht ch z => ?_⟩
  rw [childTransition_inv hζ k t ch z, Matrix.mul_apply, Fin.sum_univ_two]
  have hc : ∀ L : GeoLetter, L.isStrain = true ∨ ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0 :=
    fun _ => Or.inr ht
  simp only [GenSort.add, GenSort.mul, GeoLetter.eval, hc, ite_true]
  rfl

theorem isScheduled_kExpr (i : ℕ) (pc k : ℤ) (hk : IsScheduledIn D i k pc) (a b : Fin 2) :
    Gen.IsScheduled D (kExpr i pc k a b) :=
  .add (.mul (.geoOwn _) (.geoChild k _ hk)) (.mul (.geoOwn _) (.geoChild k _ hk))

theorem fromSeed_kExpr (i : ℕ) (pc k : ℤ) (a b : Fin 2) : Gen.FromSeed 𝒮 (kExpr i pc k a b) :=
  .add (.mul (.geo _ _) (.geo _ _)) (.mul (.geo _ _) (.geo _ _))

end AVRegularity.Providers.GenSem
end
end

section
section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **D5: the transition coefficients as context expressions.** The recursion of `transitionT`
 differentiates `T_{I,A}` in the recentering offset of the coarser context; along a
recentering the derivative is the old-label derivative (K3)(a) `dOld` at the recentered context
(recenterings compose, the final phase moves by `h/ε`). Hence `tExpr I A`, built with `kExpr`,
`dOld`, sums and products, denotes `T_{I,A}` at every recentered context, without any regularity
assumption (the junk derivatives agree on both sides). -/

/-- The expression of `T_{I,A}` for the child of the slot `k`. -/
def tExpr (i : ℕ) (pc k : ℤ) : List (Fin 2) → List (Fin 2) → Gen .ctx i pc
  | [], [] => Gen.time (.const 1)
  | [], _ :: _ => Gen.time (.const 0)
  | j :: I, [] =>
      Gen.add (Gen.add (Gen.mul (kExpr i pc k 0 j) (Gen.dOld 0 (tExpr i pc k I [])))
        (Gen.mul (kExpr i pc k 1 j) (Gen.dOld 1 (tExpr i pc k I [])))) (Gen.time (.const 0))
  | j :: I, a :: A₀ =>
      Gen.add (Gen.add (Gen.mul (kExpr i pc k 0 j) (Gen.dOld 0 (tExpr i pc k I (a :: A₀))))
        (Gen.mul (kExpr i pc k 1 j) (Gen.dOld 1 (tExpr i pc k I (a :: A₀)))))
        (Gen.mul (kExpr i pc k a j) (tExpr i pc k I A₀))

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports}

theorem isScheduled_tExpr {i : ℕ} {pc k : ℤ} (hk : IsScheduledIn D i k pc) :
    ∀ I A, Gen.IsScheduled D (tExpr i pc k I A)
  | [], [] => .timeConst _
  | [], _ :: _ => .timeConst _
  | j :: I, [] => .add (.add (.mul (isScheduled_kExpr i pc k hk 0 j)
      (.dOld 0 (isScheduled_tExpr hk I []))) (.mul (isScheduled_kExpr i pc k hk 1 j)
      (.dOld 1 (isScheduled_tExpr hk I [])))) (.timeConst _)
  | j :: I, a :: A₀ => .add (.add (.mul (isScheduled_kExpr i pc k hk 0 j)
      (.dOld 0 (isScheduled_tExpr hk I _))) (.mul (isScheduled_kExpr i pc k hk 1 j)
      (.dOld 1 (isScheduled_tExpr hk I _)))) (.mul (isScheduled_kExpr i pc k hk a j)
      (isScheduled_tExpr hk I A₀))

theorem fromSeed_tExpr {i : ℕ} {pc k : ℤ} : ∀ I A, Gen.FromSeed 𝒮 (tExpr i pc k I A)
  | [], [] => .time _
  | [], _ :: _ => .time _
  | j :: I, [] => .add (.add (.mul (fromSeed_kExpr i pc k 0 j) (.dOld 0 (fromSeed_tExpr I [])))
      (.mul (fromSeed_kExpr i pc k 1 j) (.dOld 1 (fromSeed_tExpr I [])))) (.time _)
  | j :: I, a :: A₀ => .add (.add (.mul (fromSeed_kExpr i pc k 0 j) (.dOld 0 (fromSeed_tExpr I _)))
      (.mul (fromSeed_kExpr i pc k 1 j) (.dOld 1 (fromSeed_tExpr I _))))
      (.mul (fromSeed_kExpr i pc k a j) (fromSeed_tExpr I A₀))

/-- The inverse chart transition along the recentered contexts of `(ch, z)`. -/
def kAlong (D : OCData) (i : ℕ) (k : ℤ) (t : ℝ) (ch : RealChain) (z : Vec 2) :
    Vec 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  fun h => (childTransition D k t (ch.recenter D h) (z + (D.eps i)⁻¹ • h))⁻¹

/-- The old-label derivative along a recentering is the derivative in the offset. -/
theorem dOld_along (hζ : IsFastProfile D.ζ) (i : ℕ) (g : GenSort.Sem .ctx) (t : ℝ)
    (ch : RealChain) (z y : Vec 2) (b : Fin 2) :
    fderiv ℝ (fun h : Vec 2 => g t ((ch.recenter D y).recenter D h)
        ((z + (D.eps i)⁻¹ • y) + (D.eps i)⁻¹ • h)) 0 (basisVec b) =
      fderiv ℝ (fun y' : Vec 2 => g t (ch.recenter D y') (z + (D.eps i)⁻¹ • y')) y (basisVec b) := by
  have e : (fun h : Vec 2 => g t ((ch.recenter D y).recenter D h)
      ((z + (D.eps i)⁻¹ • y) + (D.eps i)⁻¹ • h)) =
      fun h => (fun y' : Vec 2 => g t (ch.recenter D y') (z + (D.eps i)⁻¹ • y')) (y + h) := by
    funext h
    simp only [recenter_recenter D hζ, smul_add, add_assoc]
  rw [e]
  set G : Vec 2 → ℝ := fun y' => g t (ch.recenter D y') (z + (D.eps i)⁻¹ • y')
  show fderiv ℝ (fun h => G (y + h)) 0 (basisVec b) = fderiv ℝ G y (basisVec b)
  rw [fderiv_comp_add_left, add_zero]

/-- **`tExpr I A` denotes `T_{I,A}` at every recentered context**, at the times where the weight
`ϖ_{i+1,k}` does not vanish. -/
theorem denotes_tExpr (hζ : IsFastProfile D.ζ) (i : ℕ) (pc k : ℤ) :
    ∀ I A, ∃ f : GenSort.Sem .ctx, Gen.Denotes D bw j₀ (tExpr i pc k I A) f ∧
      ∀ t, ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0 → ∀ ch z y,
        f t (ch.recenter D y) (z + (D.eps i)⁻¹ • y) = transitionT (kAlong D i k t ch z) I A y
  | [], [] => ⟨_, .time _, fun _ _ _ _ _ => rfl⟩
  | [], _ :: _ => ⟨_, .time _, fun _ _ _ _ _ => rfl⟩
  | j :: I, A => by
    obtain ⟨fK0, hK0, hvK0⟩ := denotes_kExpr (bw := bw) (j₀ := j₀) hζ i pc k 0 j
    obtain ⟨fK1, hK1, hvK1⟩ := denotes_kExpr (bw := bw) (j₀ := j₀) hζ i pc k 1 j
    obtain ⟨fI, hI, hvI⟩ := denotes_tExpr hζ i pc k I A
    have hder : ∀ t, ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0 → ∀ ch z y (b : Fin 2),
        fderiv ℝ (fun h : Vec 2 => fI t ((ch.recenter D y).recenter D h)
          ((z + (D.eps i)⁻¹ • y) + (D.eps i)⁻¹ • h)) 0 (basisVec b) =
        fderiv ℝ (transitionT (kAlong D i k t ch z) I A) y (basisVec b) := by
      intro t ht ch z y b
      rw [dOld_along hζ i fI t ch z y b]
      congr 2
      funext y'
      exact hvI t ht ch z y'
    have hK : ∀ t ch z y (a : Fin 2), (kAlong D i k t ch z y) a j =
        (childTransition D k t (ch.recenter D y) (z + (D.eps i)⁻¹ • y))⁻¹ a j := fun _ _ _ _ _ => rfl
    cases A with
    | nil =>
      refine ⟨_, .add (.add (.mul hK0 (.dOld 0 hI)) (.mul hK1 (.dOld 1 hI))) (.time _),
        fun t ht ch z y => ?_⟩
      show (fK0 t _ _ * _ + fK1 t _ _ * _) + _ = _
      rw [hvK0 t ht, hvK1 t ht]
      beta_reduce
      rw [hder t ht, hder t ht]
      simp only [transitionT, Fin.sum_univ_two, kAlong, TimeLetter.eval, GenSort.ofTime, add_zero]
    | cons a A₀ =>
      obtain ⟨fKa, hKa, hvKa⟩ := denotes_kExpr (bw := bw) (j₀ := j₀) hζ i pc k a j
      obtain ⟨fA, hA, hvA⟩ := denotes_tExpr hζ i pc k I A₀
      refine ⟨_, .add (.add (.mul hK0 (.dOld 0 hI)) (.mul hK1 (.dOld 1 hI))) (.mul hKa hA),
        fun t ht ch z y => ?_⟩
      show (fK0 t _ _ * _ + fK1 t _ _ * _) + fKa t _ _ * fA t _ _ = _
      rw [hvK0 t ht, hvK1 t ht, hvKa t ht, hvA t ht]
      beta_reduce
      rw [hder t ht, hder t ht]
      simp only [transitionT, Fin.sum_univ_two, kAlong]

end AVRegularity.Providers.GenSem
end
end

section
/-! **D5: the transfer to the coarser chart is a context expression.** Given family expressions of
the finer outputs (the entries `fluxCoeff (fop k t 𝒜^♮) d I 0` at the appended child, where the
weight of the finer slot does not vanish), the transferred array `transferAt` of the slot `pc` of
level `i` is denoted by one scheduled, seed-provenanced context expression: the finite sum over the
scheduled finer slots of `J⁻¹ · (K6)-evaluation · T_{I,A}` (`kExpr`, `Gen.evalChild`, `tExpr`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.Providers.GenSem

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports}

/-- The component `κ` of the transported coefficient at the offset `0`. -/
theorem transportedCoeff_apply (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Dγ : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (r : ℕ) (A : DerivativeWord2 r) (κ : Fin 2) :
    transportedCoeff K Dγ B r A 0 κ = ∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1),
      ∑ i₀ : Fin 2, K 0 κ i₀ * B d I i₀ * transitionT K (List.ofFn I) (List.ofFn A) 0 := rfl

theorem kAlong_zero (hζ : IsFastProfile D.ζ) (i : ℕ) (k : ℤ) (t : ℝ) (ch : RealChain)
    (z : Vec 2) : kAlong D i k t ch z 0 = (childTransition D k t ch z)⁻¹ := by
  simp [kAlong, recenter_zero D hζ]

/-- **D5: the transfer is a context expression.** -/
theorem transferAt_ctxRep (hζ : IsFastProfile D.ζ) (i : ℕ) (pc : ℤ)
    (P : ℝ → RealChain → Vec 2 → Prop) (lam : ℝ) (Dγ : ℕ) (fop : FamFluxOp) (d' : ℕ)
    (β : DerivativeWord2 (d' - 1)) (κ : Fin 2)
    (hfin : {k : ℤ | Odd k ∧ IsScheduledIn D i k pc}.Finite)
    (hB : ∀ k : ℤ, Odd k → IsScheduledIn D i k pc → ∀ d ∈ Finset.Icc (d' - 1 + 1) Dγ,
      ∀ (I : DerivativeWord2 (d - 1)) (i₀ : Fin 2), ∃ c : Gen .fam (i + 1) k,
        Gen.IsScheduled D c ∧ Gen.FromSeed 𝒮 c ∧ ∃ fc : GenSort.Sem .fam,
          Gen.Denotes D bw j₀ c fc ∧ ∀ t ch z, P t ch z →
            ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0 →
            fc t (ch.appendChild D k t z) = fluxCoeff (fop k t (ch.appendChild D k t z)) d I 0 i₀) :
    ∃ e : Gen .ctx i pc, CtxRep D bw j₀ 𝒮 P
      (fun t ch z => transferAt D (i + 1) pc lam Dγ fop t ch z d' β κ) e := by
  classical
  set C : ℝ := (D.kap i * D.eps i ^ (d' - 2))⁻¹ * lam with hC
  -- one finer slot
  have hslot : ∀ k ∈ hfin.toFinset, ∃ e : Gen .ctx i pc, CtxRep D bw j₀ 𝒮 P
      (fun t ch z => ocCutoff D.α D.q D.Λ (i + 1) k t *
        transportedCoeff (kAlong D i k t ch z) Dγ
          (fun d I => fluxCoeff (fop k t (ch.appendChild D k t z)) d I 0) (d' - 1) β 0 κ) e := by
    intro k hk
    have hk' : Odd k ∧ IsScheduledIn D i k pc := hfin.mem_toFinset.mp hk
    obtain ⟨e, he⟩ := CtxRep.finsetSum (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := i) (pc := pc)
      (P := P) (Finset.Icc (d' - 1 + 1) Dγ)
      (φ := fun d t ch z => ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2,
        (childTransition D k t ch z)⁻¹ κ i₀ *
          (ocCutoff D.α D.q D.Λ (i + 1) k t * fluxCoeff (fop k t (ch.appendChild D k t z)) d I 0 i₀) *
          transitionT (kAlong D i k t ch z) (List.ofFn I) (List.ofFn β) 0) (fun d hd => by
        refine CtxRep.finsetSum _ fun I _ => CtxRep.finsetSum _ fun i₀ _ => ?_
        obtain ⟨c, hcs, hcf, fc, hcd, hcv⟩ := hB k hk'.1 hk'.2 d hd I i₀
        obtain ⟨fK, hKd, hKv⟩ := denotes_kExpr (bw := bw) (j₀ := j₀) hζ i pc k κ i₀
        obtain ⟨fT, hTd, hTv⟩ := denotes_tExpr (bw := bw) (j₀ := j₀) hζ i pc k (List.ofFn I)
          (List.ofFn β)
        have hE := ctxRep_evalChild (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) P k hk' hcs hcf hcd
          (ψ := fun t A => fluxCoeff (fop k t A) d I 0 i₀) hcv
        obtain ⟨hEs, hEf, fE, hEd, hEv⟩ := hE
        -- the child letters are gated by the weight, which also multiplies the product
        refine ⟨_, ⟨.mul (.mul (isScheduled_kExpr i pc k hk'.2 κ i₀) hEs) (isScheduled_tExpr hk'.2 _ _),
          .mul (.mul (fromSeed_kExpr i pc k κ i₀) hEf) (fromSeed_tExpr _ _), _,
          .mul (.mul hKd hEd) hTd, fun t ch z hP => ?_⟩⟩
        show fK t ch z * fE t ch z * fT t ch z = _
        rw [hEv t ch z hP]
        by_cases h0 : ocCutoff D.α D.q D.Λ (i + 1) k t = 0
        · simp [h0]
        · have hT0 := hTv t h0 ch z 0
          simp only [recenter_zero D hζ, smul_zero, add_zero] at hT0
          rw [hKv t h0 ch z, hT0])
    refine ⟨e, he.congr fun t ch z _ => ?_⟩
    rw [transportedCoeff_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i₀ _ => ?_
    rw [kAlong_zero hζ]
    ring
  obtain ⟨eS, heS⟩ := CtxRep.finsetSum (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := i) (pc := pc)
    (P := P) hfin.toFinset hslot
  refine ⟨_, ((CtxRep.const C).mul heS).congr fun t ch z _ => ?_⟩
  have hfs : (∑ᶠ (k : ℤ) (_ : Odd k ∧ IsScheduledIn D i k pc),
      ocCutoff D.α D.q D.Λ (i + 1) k t •
        transportedCoeff (fun h => (childTransition D k t (ch.recenter D h)
          (z + (D.eps i)⁻¹ • h))⁻¹) Dγ
          (fun d I => fluxCoeff (fop k t (ch.appendChild D k t z)) d I 0) (d' - 1) β 0) =
      ∑ k ∈ hfin.toFinset, ocCutoff D.α D.q D.Λ (i + 1) k t •
        transportedCoeff (fun h => (childTransition D k t (ch.recenter D h)
          (z + (D.eps i)⁻¹ • h))⁻¹) Dγ
          (fun d I => fluxCoeff (fop k t (ch.appendChild D k t z)) d I 0) (d' - 1) β 0 :=
    finsum_mem_eq_finite_toFinset_sum _ hfin
  simp only [transferAt, Nat.add_sub_cancel]
  rw [hfs, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  congr 1

end AVRegularity.Providers.GenSem

namespace AVRegularity.Providers.GenSem

/-- The finer slots scheduled in a slot form a finite set (the weights of the finer level have
bounded support and the output window is bounded). -/
theorem scheduledSlots_finite (D : OCData) (i : ℕ) (pc : ℤ)
    (hτ : 0 < ocTau D.α D.q D.Λ (i + 1)) :
    {k : ℤ | Odd k ∧ IsScheduledIn D i k pc}.Finite := by
  set τ' := ocTau D.α D.q D.Λ (i + 1)
  set a := ((pc : ℝ) - 61 / 48) * ocTau D.α D.q D.Λ i
  set b := ((pc : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i
  refine (Set.finite_Icc (⌊a / τ' - 2⌋) (⌈b / τ' + 2⌉)).subset fun k hk => ?_
  obtain ⟨-, t, ht1, ht2⟩ := hk
  have hne : ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0 := ht1
  have hpos : 0 < 5 / 2 - 2 * |t - (k : ℝ) * τ'| / τ' := by
    by_contra hc
    exact hne (Real.smoothTransition.zero_of_nonpos (not_lt.mp hc))
  have hab : |t - (k : ℝ) * τ'| < 5 / 4 * τ' := by
    have h1 : 2 * |t - (k : ℝ) * τ'| / τ' < 5 / 2 := by linarith
    rw [div_lt_iff₀ hτ] at h1
    linarith
  have ht : a ≤ t ∧ t ≤ b := ht2
  rw [abs_lt] at hab
  have hk1 : a / τ' - 2 ≤ (k : ℝ) := by
    rw [div_sub' (ne_of_gt hτ), div_le_iff₀ hτ]
    nlinarith
  have hk2 : (k : ℝ) ≤ b / τ' + 2 := by
    rw [div_add' _ _ _ (ne_of_gt hτ), le_div_iff₀ hτ]
    nlinarith
  exact ⟨Int.floor_le_iff.mpr (by linarith), Int.le_ceil_iff.mpr (by linarith)⟩

end AVRegularity.Providers.GenSem
end
end
end
