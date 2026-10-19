-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Majorant.Unique
public import AVRegularity.Proofs.GenSem.ChainMetric
public import AVRegularity.Proofs.GenSem.Transfer.Assemble
import AVRegularity.Proofs.CascadeInvariants.Scales
public import AVRegularity.Proofs.GenSem.Finer.CovLetterArr
import AVRegularity.Proofs.GenSem.CoeffArr.MonoSource

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the certified old coefficients as leaves.** A certified stage `G`
(`G.OldCert 𝒮o μo Lo Co`, for instance a context-certified stage) supplies, for every old coefficient (edge, order, word, component,
slot), a generated expression `oldExpr`, its function and a holomorphic extension `oldExt` whose
mode suprema give the ledger sizes. The leaf map `oldLeaf` sends the wrapped expression
`oldWrap idx` (wrapped, so that it is never a node built by the ledger)
to the exact profile `ctxModeSup (oldExt idx)`, and every other expression to `none`. The wrapping
`oldWrap idx = 1 · oldExpr idx + 0 · code(idx)` carries an injective code of the index
(`oldCode`, from the countability of the indices), so that distinct old coefficients have distinct
leaves, each with its own certified profile (`oldLeaf_oldWrap`), even when their chosen expressions
coincide.

`leavesCertified_oldLeaf`: the leaf map is certified, given that the denotations of the exports of
the registry `𝒮o` are unique on the output domains (with the cascade exports): every denotation of an
old expression agrees with the certified function on `J_𝗉` and the admissible chains,
so the certified extension works for it. -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- An old coefficient: edge, order, word, component and slot. -/
structure OldIdx (G : GenStage D hr Dm b j₀) where
  v : CompIn G.comps
  u : CompIn G.comps
  γ : G.fam.Γ v u
  d : ℕ
  α : DerivativeWord2 (d - 1)
  c : Fin 2
  p : OddSlot

/-- The wrapping `1 · e + 0 · n` of an expression with the code `n`. -/
def wrapE (n : ℕ) {i : ℕ} {p : ℤ} (e : Gen .ctx i p) : Gen .ctx i p :=
  Gen.add (Gen.mul (Gen.time (.const 1)) e) (Gen.mul (Gen.time (.const 0)) (Gen.time (.const n)))

/-- The old coefficients are countable. -/
theorem countable_oldIdx (G : GenStage D hr Dm b j₀) : Countable (OldIdx G) := by
  classical
  let := G.fam.fintypeΓ
  refine Function.Injective.countable (β := Σ (v u : CompIn G.comps) (_ : G.fam.Γ v u) (d : ℕ)
    (_ : DerivativeWord2 (d - 1)) (_ : Fin 2), OddSlot)
    (f := fun x => ⟨x.v, x.u, x.γ, x.d, x.α, x.c, x.p⟩) ?_
  rintro ⟨v, u, γ, d, α, c, p⟩ ⟨v', u', γ', d', α', c', p'⟩ h
  cases h
  rfl

/-- An injective code of the old coefficients. -/
def oldCode (G : GenStage D hr Dm b j₀) : OldIdx G → ℕ :=
  Classical.choose (@exists_injective_nat (OldIdx G) (countable_oldIdx G))

theorem oldCode_injective (G : GenStage D hr Dm b j₀) : Function.Injective (oldCode G) :=
  Classical.choose_spec (@exists_injective_nat (OldIdx G) (countable_oldIdx G))

variable {𝒮o : SeedExports} {μo : Comp → ℝ} {Lo : ℕ} {Co : ℝ} {G : GenStage D hr Dm b j₀}

/-- The certified function of an old coefficient. -/
def oldFun (hcert : G.OldCert 𝒮o μo Lo Co) (x : OldIdx G) : GenSort.Sem .ctx :=
  Classical.choose ((Classical.choose_spec (hcert x.v x.u x.γ)).2.2 x.d x.α x.c) x.p

/-- The certified extension of an old coefficient. -/
def oldExt (hcert : G.OldCert 𝒮o μo Lo Co) (x : OldIdx G) :
    ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ :=
  Classical.choose (Classical.choose_spec
    ((Classical.choose_spec (hcert x.v x.u x.γ)).2.2 x.d x.α x.c)) x.p

theorem oldFunExt_spec (hcert : G.OldCert 𝒮o μo Lo Co) (x : OldIdx G) :
    IsGeneratedCtxFrom D b j₀ 𝒮o G.level x.p.1 (oldFun hcert x) ∧
      IsHolExtension D b j₀ G.level x.p.1 (oldFun hcert x) (oldExt hcert x) :=
  ⟨((Classical.choose_spec (Classical.choose_spec
      ((Classical.choose_spec (hcert x.v x.u x.γ)).2.2 x.d x.α x.c))).1 x.p).1,
    ((Classical.choose_spec (Classical.choose_spec
      ((Classical.choose_spec (hcert x.v x.u x.γ)).2.2 x.d x.α x.c))).1 x.p).2.1⟩

/-- The generated expression of an old coefficient. -/
def oldExpr (hcert : G.OldCert 𝒮o μo Lo Co) (x : OldIdx G) : Gen .ctx G.level x.p.1 :=
  Classical.choose (oldFunExt_spec hcert x).1

theorem oldExpr_spec (hcert : G.OldCert 𝒮o μo Lo Co) (x : OldIdx G) :
    Gen.IsScheduled D (oldExpr hcert x) ∧ Gen.FromSeed 𝒮o (oldExpr hcert x) ∧
      Gen.Denotes D b j₀ (oldExpr hcert x) (oldFun hcert x) :=
  Classical.choose_spec (oldFunExt_spec hcert x).1

theorem oldExt_spec (hcert : G.OldCert 𝒮o μo Lo Co) (x : OldIdx G) :
    IsHolExtension D b j₀ G.level x.p.1 (oldFun hcert x) (oldExt hcert x) :=
  (oldFunExt_spec hcert x).2

/-- The wrapped expression of an old coefficient. -/
def oldWrap (hcert : G.OldCert 𝒮o μo Lo Co) (x : OldIdx G) : Gen .ctx G.level x.p.1 :=
  wrapE (oldCode G x) (oldExpr hcert x)

open scoped Classical in
/-- **The leaf map of the old coefficients.** -/
def oldLeaf (hcert : G.OldCert 𝒮o μo Lo Co) :
    ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞) :=
  fun {s i p} e =>
    if h : ∃ x : OldIdx G, (⟨.ctx, G.level, x.p.1, oldWrap hcert x⟩ :
        Σ (s : GenSort) (i : ℕ) (p : ℤ), Gen s i p) = ⟨s, i, p, e⟩ then
      some fun mres h' => ctxModeSup D b j₀ G.level (Classical.choose h).p.1
        (oldExt hcert (Classical.choose h)) mres h'
    else none

/-- The code carried by a wrapped expression (`0` for any other expression). -/
def codeOf : {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → ℝ
  | _, _, _, .add _ (.mul _ (.time (.const r))) => r
  | _, _, _, _ => 0

theorem codeOf_wrapE (n : ℕ) {i : ℕ} {p : ℤ} (e : Gen .ctx i p) : codeOf (wrapE n e) = n := rfl

/-- Distinct old coefficients have distinct wrapped expressions. -/
theorem oldWrap_inj (hcert : G.OldCert 𝒮o μo Lo Co) {x y : OldIdx G}
    (h : (⟨.ctx, G.level, x.p.1, oldWrap hcert x⟩ : Σ (s : GenSort) (i : ℕ) (p : ℤ), Gen s i p) =
      ⟨.ctx, G.level, y.p.1, oldWrap hcert y⟩) : x = y := by
  apply oldCode_injective G
  have hc := congrArg (fun σ : Σ (s : GenSort) (i : ℕ) (p : ℤ), Gen s i p => codeOf σ.2.2.2) h
  simp only [oldWrap, codeOf_wrapE] at hc
  exact_mod_cast hc

/-- **The leaf of an old coefficient carries its own certified profile.** -/
theorem oldLeaf_oldWrap (hcert : G.OldCert 𝒮o μo Lo Co) (x : OldIdx G) :
    oldLeaf hcert (oldWrap hcert x) =
      some fun mres h' => ctxModeSup D b j₀ G.level x.p.1 (oldExt hcert x) mres h' := by
  classical
  have h : ∃ y : OldIdx G, (⟨.ctx, G.level, y.p.1, oldWrap hcert y⟩ :
      Σ (s : GenSort) (i : ℕ) (p : ℤ), Gen s i p) = ⟨.ctx, G.level, x.p.1, oldWrap hcert x⟩ :=
    ⟨x, rfl⟩
  have hy : Classical.choose h = x := oldWrap_inj hcert (Classical.choose_spec h)
  simp only [oldLeaf, h, ↓reduceDIte]
  rw [hy]

variable (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hb : 0 < b)
  (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
    2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
  (hexpU : ∀ {i p} (e : Gen .ctx i p), 𝒮o e → ∀ f f', Gen.Denotes D b j₀ e f →
      Gen.Denotes D b j₀ e f' → AgreeOn D b j₀ i p .ctx f f')

include hΛ hζ hb hstart hexpU in
/-- **The leaf map of the old coefficients is certified.** -/
theorem leavesCertified_oldLeaf (hcert : G.OldCert 𝒮o μo Lo Co) :
    LeavesCertified D b j₀ (oldLeaf hcert) := by
  classical
  refine ⟨fun s i p e hs => ?_, fun i p e B hB f hf => ?_⟩
  · simp only [oldLeaf]
    split_ifs with h
    · obtain ⟨x, hx⟩ := h
      exact absurd (congrArg Sigma.fst hx).symm hs
    · rfl
  · simp only [oldLeaf] at hB
    split_ifs at hB with h
    have hspec := Classical.choose_spec h
    generalize Classical.choose h = y at hspec hB
    cases hspec
    simp only [Option.some.injEq] at hB
    subst hB
    refine ⟨oldExt hcert y, ?_, fun _ _ => le_rfl⟩
    obtain ⟨hs, hfs, hden⟩ := oldExpr_spec hcert y
    have hext := oldExt_spec hcert y
    unfold oldWrap wrapE at hf
    cases hf with
    | @add _ _ _ _ _ fx fz hx hz =>
      cases hx with
      | @mul _ _ _ _ _ fa fb hc hd' =>
        cases hc
        cases hz with
        | mul hc0 hcn =>
          cases hc0
          cases hcn
          refine ⟨hext.1, hext.2.1, fun ch t ht ζ hA => ?_⟩
          have hag := denotes_agreeOn_of_exports hΛ hζ hb hstart hexpU hd' hfs hs hden
          rw [hext.2.2 ch t ht ζ hA]
          show ((oldFun hcert y t ch ζ : ℝ) : ℂ) =
            ((1 * fb t ch ζ + 0 * _ : ℝ) : ℂ)
          rw [one_mul, zero_mul, add_zero, hag t ht ch hA ζ]

end AVRegularity.Providers.CascadeInvariants
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the ledger sum from structural norms.** The sum of `successor_ledger`,
`∑_h e^{3π bw|h|}(1+|h|)^{L} ⨆_𝗉 genMode (e 𝗉) mres h` (slot supremum inside each mode), is at most
`wsum (3π bw) L (e^{-a|·|}) · M` whenever the structural norms of all `e 𝗉` at an outer rate `a`
are at most `M` (`ledgerSum_le`): pointwise, `genMode (e 𝗉) mres h ≤ e^{-a|h|} genNorm (e 𝗉) a mres 0`
(`genMode_le_exp_mul_genNorm`), uniformly in the slot. For `a > 3π bw` the weight factor is finite
(`wsum_expProfile_lt_top`). -/

open AVRegularity AVRegularity.Providers.Majorant

variable (D : OCData) (κc : MajConsts) (Δ a₀ : ℝ)
  (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞))

theorem modeWeight_zero_eq (a : ℝ) (h : ℤ) :
    modeWeight a 0 h = ENNReal.ofReal (Real.exp (a * |(h : ℝ)|)) := by
  simp [modeWeight]

/-- **Pointwise decay at the outer rate.** -/
theorem genMode_le_exp_mul_genNorm (ha₀ : 0 ≤ a₀) {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p)
    {a : ℝ} (ha : 0 ≤ a) (mres : ℝ) (h : ℤ) (t : ℝ) :
    genMode D κc Δ leaf e mres h t ≤
      ENNReal.ofReal (Real.exp (-(a * |(h : ℝ)|))) * genNorm D κc Δ a₀ leaf e a mres 0 t := by
  have hw := genMode_le_of_genNorm D κc Δ a₀ leaf ha₀ e ha mres h t
  rw [modeWeight_zero_eq] at hw
  have hinv : ENNReal.ofReal (Real.exp (-(a * |(h : ℝ)|))) *
      ENNReal.ofReal (Real.exp (a * |(h : ℝ)|)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  calc genMode D κc Δ leaf e mres h t
      = ENNReal.ofReal (Real.exp (-(a * |(h : ℝ)|))) *
          (ENNReal.ofReal (Real.exp (a * |(h : ℝ)|)) * genMode D κc Δ leaf e mres h t) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ _ := mul_le_mul_right hw _

/-- **The ledger sum of a slot-indexed family of expressions** (time suprema over the output
windows inside each mode). -/
theorem ledgerSum_le (ha₀ : 0 ≤ a₀) {i : ℕ} (e : (p : OddSlot) → Gen .ctx i p.1) {a : ℝ}
    (ha : 0 ≤ a) (c : ℝ) (L : ℕ) (mres : ℝ) (M : ℝ≥0∞)
    (hM : ∀ p, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p.1, genNorm D κc Δ a₀ leaf (e p) a mres 0 t ≤ M) :
    ∑' h : ℤ, ENNReal.ofReal (Real.exp (c * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L) *
        ⨆ p : OddSlot, ⨆ t ∈ ocPulseWindow D.α D.q D.Λ i p.1, genMode D κc Δ leaf (e p) mres h t ≤
      wsum c L (expProfile 1 a) * M := by
  unfold wsum
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun h => ?_
  rw [mul_assoc]
  refine mul_le_mul_right ?_ _
  have hp : ∀ p, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p.1, genMode D κc Δ leaf (e p) mres h t ≤
      ENNReal.ofReal (Real.exp (-(a * |(h : ℝ)|))) * M := fun p t ht =>
    (genMode_le_exp_mul_genNorm D κc Δ a₀ leaf ha₀ (e p) ha mres h t).trans
      (mul_le_mul_right (hM p t ht) _)
  refine (iSup_le fun p => iSup₂_le (hp p)).trans (le_of_eq ?_)
  simp [expProfile]

end AVRegularity.Providers.CascadeInvariants
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: explicit finite sums of expressions.** `genSumList l` is the right-nested sum
`l₁ + (l₂ + (⋯ + 0))` of a list of expressions. It represents the sum of the represented functions
(`CtxRep.genSumList`), and its structural norm is at most the sum of the norms, when no node of the
sum is a certified leaf (`genNorm_genSumList_le`). This makes the existential `CtxRep.finsetSum`
explicit, so that the ledger can bound the expressions it builds. -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

/-- The right-nested sum of a list of expressions, `0` for the empty list. -/
def genSumList {s : GenSort} {i : ℕ} {p : ℤ} : List (Gen s i p) → Gen s i p
  | [] => Gen.time (.const 0)
  | e :: es => Gen.add e (genSumList es)

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports}

theorem CtxRep.genSumList {i : ℕ} {pc : ℤ} {P : ℝ → RealChain → Vec 2 → Prop} {κ : Type*}
    (l : List κ) (φ : κ → ℝ → RealChain → Vec 2 → ℝ) (f : κ → Gen .ctx i pc)
    (h : ∀ k ∈ l, CtxRep D bw j₀ 𝒮 P (φ k) (f k)) :
    CtxRep D bw j₀ 𝒮 P (fun t ch z => (l.map fun k => φ k t ch z).sum)
      (CascadeInvariants.genSumList (l.map f)) := by
  induction l with
  | nil => exact (GenSem.CtxRep.const 0).congr fun _ _ _ _ => by simp
  | cons a l ih =>
    have h₁ := h a List.mem_cons_self
    have h₂ := ih fun k hk => h k (List.mem_cons_of_mem a hk)
    exact (h₁.add h₂).congr fun t ch z _ => by simp

theorem CtxRep.genSumFinset {i : ℕ} {pc : ℤ} {P : ℝ → RealChain → Vec 2 → Prop} {κ : Type*}
    (s : Finset κ) (φ : κ → ℝ → RealChain → Vec 2 → ℝ) (f : κ → Gen .ctx i pc)
    (h : ∀ k ∈ s, CtxRep D bw j₀ 𝒮 P (φ k) (f k)) :
    CtxRep D bw j₀ 𝒮 P (fun t ch z => ∑ k ∈ s, φ k t ch z)
      (CascadeInvariants.genSumList (s.toList.map f)) :=
  (CtxRep.genSumList s.toList φ f fun k hk => h k (Finset.mem_toList.mp hk)).congr
    fun _ _ _ _ => Finset.sum_map_toList s _

variable (κc : MajConsts) (Δ a₀ : ℝ)
  (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞))

/-- The norm of a time-only constant is at most its absolute value. -/
theorem genNorm_const_le {s : GenSort} {i : ℕ} {p : ℤ} (c : ℝ)
    (hl : leaf (Gen.time (s := s) (i := i) (p := p) (.const c)) = none) (a mres : ℝ) (L : ℕ)
    (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.time (s := s) (i := i) (p := p) (.const c)) a mres L t ≤
      ENNReal.ofReal |c| := by
  simp only [genNorm, hl, Option.elim, TimeLetter.eval]
  exact le_rfl

/-- **The structural norm of an explicit sum** is at most the sum of the norms. -/
theorem genNorm_genSumList_le {s : GenSort} {i : ℕ} {p : ℤ}
    (hadd : ∀ x y : Gen s i p, leaf (Gen.add x y) = none)
    (h0 : leaf (Gen.time (s := s) (i := i) (p := p) (.const 0)) = none) (a mres : ℝ) (L : ℕ)
    (t : ℝ) (l : List (Gen s i p)) :
    genNorm D κc Δ a₀ leaf (CascadeInvariants.genSumList l) a mres L t ≤
      (l.map fun e => genNorm D κc Δ a₀ leaf e a mres L t).sum := by
  induction l with
  | nil => simpa [CascadeInvariants.genSumList] using genNorm_const_le κc Δ a₀ leaf 0 h0 a mres L t
  | cons e es ih =>
    simp only [CascadeInvariants.genSumList, genNorm, hadd, Option.elim, List.map_cons, List.sum_cons]
    exact add_le_add le_rfl ih

end AVRegularity.Providers.CascadeInvariants
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the explicit transfer expression.** The transferred coefficient
`transferAt D (i+1) pc lam Dγ fop … d' β κ` of the slot `pc` of level `i` is denoted by the explicit
expression `transferExpr`: the constant `C = (κ_i ε_i^{d'-2})⁻¹ λ` times the explicit sum, over the
scheduled finer slots `k`, the orders `d`, the words `I` and the components `i₀`, of
`J⁻¹_{κ i₀} · (evalChild evaluation of c_{k,d,I,i₀}) · T_{I,β}` (`transferTerm`), given family expressions
`c_{k,d,I,i₀}` of the finer outputs (`ctxRep_transferExpr`). This is `transferAt_ctxRep`
with the sums made explicit. -/

open AVRegularity.Providers.GenSem

/-- One summand `J⁻¹_{κ i₀} · ϖ_k c(t, 𝒜^♮) · T_{I,β}` of the transfer. -/
def transferTerm (i : ℕ) (pc k : ℤ) (κ : Fin 2) {d : ℕ} (I : DerivativeWord2 (d - 1)) (i₀ : Fin 2)
    {d' : ℕ} (β : DerivativeWord2 (d' - 1)) (c : Gen .fam (i + 1) k) : Gen .ctx i pc :=
  Gen.mul (Gen.mul (kExpr i pc k κ i₀) (Gen.evalChild k c))
    (tExpr i pc k (List.ofFn I) (List.ofFn β))

/-- **The explicit transfer expression.** -/
def transferExpr (i : ℕ) (pc : ℤ) (C : ℝ) (S : Finset ℤ) (Dγ d' : ℕ)
    (β : DerivativeWord2 (d' - 1)) (κ : Fin 2)
    (c : (k : ℤ) → (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Gen .fam (i + 1) k) :
    Gen .ctx i pc :=
  Gen.mul (Gen.time (.const C)) (genSumList (S.toList.map fun k =>
    genSumList ((Finset.Icc (d' - 1 + 1) Dγ).toList.map fun d =>
      genSumList ((Finset.univ : Finset (DerivativeWord2 (d - 1))).toList.map fun I =>
        genSumList ((Finset.univ : Finset (Fin 2)).toList.map fun i₀ =>
          transferTerm i pc k κ I i₀ β (c k d I i₀))))))

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports}

/-- **The explicit transfer expression denotes the transferred coefficient.** -/
theorem ctxRep_transferExpr (hζ : IsFastProfile D.ζ) (i : ℕ) (pc : ℤ)
    (P : ℝ → RealChain → Vec 2 → Prop) (lam : ℝ) (Dγ : ℕ) (fop : FamFluxOp) (d' : ℕ)
    (β : DerivativeWord2 (d' - 1)) (κ : Fin 2)
    (hfin : {k : ℤ | Odd k ∧ IsScheduledIn D i k pc}.Finite)
    (c : (k : ℤ) → (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Gen .fam (i + 1) k)
    (hc : ∀ k : ℤ, Odd k → IsScheduledIn D i k pc → ∀ d ∈ Finset.Icc (d' - 1 + 1) Dγ,
      ∀ (I : DerivativeWord2 (d - 1)) (i₀ : Fin 2),
        Gen.IsScheduled D (c k d I i₀) ∧ Gen.FromSeed 𝒮 (c k d I i₀) ∧
        ∃ fc : GenSort.Sem .fam, Gen.Denotes D bw j₀ (c k d I i₀) fc ∧ ∀ t ch z, P t ch z →
          ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0 →
          fc t (ch.appendChild D k t z) = fluxCoeff (fop k t (ch.appendChild D k t z)) d I 0 i₀) :
    CtxRep D bw j₀ 𝒮 P (fun t ch z => transferAt D (i + 1) pc lam Dγ fop t ch z d' β κ)
      (transferExpr i pc ((D.kap i * D.eps i ^ (d' - 2))⁻¹ * lam) hfin.toFinset Dγ d' β κ c) := by
  classical
  set C : ℝ := (D.kap i * D.eps i ^ (d' - 2))⁻¹ * lam with hC
  -- one summand
  have hterm : ∀ k ∈ hfin.toFinset, ∀ d ∈ Finset.Icc (d' - 1 + 1) Dγ,
      ∀ (I : DerivativeWord2 (d - 1)) (i₀ : Fin 2),
      CtxRep D bw j₀ 𝒮 P (fun t ch z => (childTransition D k t ch z)⁻¹ κ i₀ *
          (ocCutoff D.α D.q D.Λ (i + 1) k t * fluxCoeff (fop k t (ch.appendChild D k t z)) d I 0 i₀) *
          transitionT (kAlong D i k t ch z) (List.ofFn I) (List.ofFn β) 0)
        (transferTerm i pc k κ I i₀ β (c k d I i₀)) := by
    intro k hk d hd I i₀
    have hk' : Odd k ∧ IsScheduledIn D i k pc := hfin.mem_toFinset.mp hk
    obtain ⟨hcs, hcf, fc, hcd, hcv⟩ := hc k hk'.1 hk'.2 d hd I i₀
    obtain ⟨fK, hKd, hKv⟩ := denotes_kExpr (bw := bw) (j₀ := j₀) hζ i pc k κ i₀
    obtain ⟨fT, hTd, hTv⟩ := denotes_tExpr (bw := bw) (j₀ := j₀) hζ i pc k (List.ofFn I)
      (List.ofFn β)
    have hE := ctxRep_evalChild (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) P k hk' hcs hcf hcd
      (ψ := fun t A => fluxCoeff (fop k t A) d I 0 i₀) hcv
    obtain ⟨hEs, hEf, fE, hEd, hEv⟩ := hE
    -- the child letters are gated by the weight, which also multiplies the product
    refine ⟨.mul (.mul (isScheduled_kExpr i pc k hk'.2 κ i₀) hEs) (isScheduled_tExpr hk'.2 _ _),
      .mul (.mul (fromSeed_kExpr i pc k κ i₀) hEf) (fromSeed_tExpr _ _), _,
      .mul (.mul hKd hEd) hTd, fun t ch z hP => ?_⟩
    show fK t ch z * fE t ch z * fT t ch z = _
    rw [hEv t ch z hP]
    by_cases h0 : ocCutoff D.α D.q D.Λ (i + 1) k t = 0
    · simp [h0]
    · have hT0 := hTv t h0 ch z 0
      simp only [recenter_zero D hζ, smul_zero, add_zero] at hT0
      rw [hKv t h0 ch z, hT0]
  -- one finer slot
  have hslot : ∀ k ∈ hfin.toFinset, CtxRep D bw j₀ 𝒮 P
      (fun t ch z => ocCutoff D.α D.q D.Λ (i + 1) k t *
        transportedCoeff (kAlong D i k t ch z) Dγ
          (fun d I => fluxCoeff (fop k t (ch.appendChild D k t z)) d I 0) (d' - 1) β 0 κ)
      (genSumList ((Finset.Icc (d' - 1 + 1) Dγ).toList.map fun d =>
        genSumList ((Finset.univ : Finset (DerivativeWord2 (d - 1))).toList.map fun I =>
          genSumList ((Finset.univ : Finset (Fin 2)).toList.map fun i₀ =>
            transferTerm i pc k κ I i₀ β (c k d I i₀))))) := by
    intro k hk
    refine (CtxRep.genSumFinset _ _ _ fun d hd =>
      CtxRep.genSumFinset _ _ _ fun I _ =>
        CtxRep.genSumFinset _ _ _ fun i₀ _ => hterm k hk d hd I i₀).congr fun t ch z _ => ?_
    rw [transportedCoeff_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i₀ _ => ?_
    rw [kAlong_zero hζ]
    ring
  refine ((GenSem.CtxRep.const C).mul (CtxRep.genSumFinset hfin.toFinset _ _ hslot)).congr
    fun t ch z _ => ?_
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

end AVRegularity.Providers.CascadeInvariants
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the structural norm of the transfer.** With no certified leaf at the level `i`
of the transfer (the leaves are the old coefficients, one level finer), the structural norm of the
pieces of the explicit transfer expression is bounded:
* `K = 2 G²` bounds an entry of `J⁻¹` (`genNorm_kExpr_le`), `G` the largest weighted sum of a
  geometric letter profile (`geoW`);
* `T_{n,r}` bounds the Piola factor `T_{I,β}` with `|I| = n`, `|β| = r` (`genNorm_tExpr_le`): each
  of its `n - r` old-label derivatives costs the Cauchy factor `C_old/(ε_i Δ)` of one reserve step, or the
  final-phase factor `2π/ε_i` of one fast weight — the factor `ε_i^{d'-d}` of the
  higher transfer.
The single-node equations (`genNorm_add_eq`, `genNorm_mul_eq`, `genNorm_evalChild_eq`) unfold one
node at a time. -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

/-- The largest weighted sum of a geometric letter profile. -/
def geoW (κc : MajConsts) (a : ℝ) (L : ℕ) : ℝ≥0∞ :=
  ⨆ (fr : GenFrame) (Lt : GeoLetter), wsum a L (κc.geo fr Lt)

/-- The bound of an entry of the inverse chart transition. -/
def kBound (κc : MajConsts) (a : ℝ) (L : ℕ) : ℝ≥0∞ := 2 * geoW κc a L ^ 2

/-- The cost of one old-label derivative of the Piola factor with `n` further derivatives. -/
def tStep (D : OCData) (κc : MajConsts) (Δ : ℝ) (i : ℕ) (T : ℝ → ℕ → ℝ≥0∞) (mres : ℝ)
    (L : ℕ) : ℝ≥0∞ :=
  (if mres + Δ ≤ 2 then κc.Cold / ENNReal.ofReal (D.eps i * Δ) * T (mres + Δ) L else ⊤) +
    ENNReal.ofReal (2 * Real.pi / D.eps i) * T mres (L + 1)

/-- The bound of the Piola factor `T_{I,A}` with `|I| = n` and `|A| = r` (`n - r` derivatives). -/
def tBound (D : OCData) (κc : MajConsts) (Δ a : ℝ) (i : ℕ) : ℕ → ℕ → ℝ → ℕ → ℝ≥0∞
  | 0, 0, _, _ => 1
  | 0, _ + 1, _, _ => 0
  | n + 1, 0, mres, L => 2 * kBound κc a L * tStep D κc Δ i (tBound D κc Δ a i n 0) mres L
  | n + 1, r + 1, mres, L =>
      2 * kBound κc a L * tStep D κc Δ i (tBound D κc Δ a i n (r + 1)) mres L +
        kBound κc a L * tBound D κc Δ a i n r mres L

variable (D : OCData) (κc : MajConsts) (Δ a₀ : ℝ)
  (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞))

theorem genNorm_add_eq {s : GenSort} {i : ℕ} {p : ℤ} {x y : Gen s i p}
    (hl : leaf (Gen.add x y) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.add x y) a mres L t =
      genNorm D κc Δ a₀ leaf x a mres L t + genNorm D κc Δ a₀ leaf y a mres L t := by
  simp only [genNorm, hl, Option.elim]

theorem genNorm_mul_eq {s : GenSort} {i : ℕ} {p : ℤ} {x y : Gen s i p}
    (hl : leaf (Gen.mul x y) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.mul x y) a mres L t =
      genNorm D κc Δ a₀ leaf x a mres L t * genNorm D κc Δ a₀ leaf y a mres L t := by
  simp only [genNorm, hl, Option.elim]

theorem genNorm_evalChild_eq {i : ℕ} {p k : ℤ} {c : Gen .fam (i + 1) k}
    (hl : leaf (Gen.evalChild (i := i) (p := p) k c) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.evalChild (i := i) (p := p) k c) a mres L t =
      ENNReal.ofReal (ocCutoff D.α D.q D.Λ (i + 1) k t) * wsum a L κc.child *
        genNorm D κc Δ a₀ leaf c a₀ mres 0 t := by
  simp only [genNorm, hl, Option.elim]

theorem genNorm_geo_le {i : ℕ} {pc : ℤ} (fr : GenFrame) (Lt : GeoLetter)
    (hl : leaf (Gen.geo (i := i) (p := pc) fr Lt) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.geo (i := i) (p := pc) fr Lt) a mres L t ≤ geoW κc a L := by
  simp only [genNorm, hl, Option.elim]
  exact le_iSup₂ (f := fun (fr : GenFrame) (Lt : GeoLetter) => wsum a L (κc.geo fr Lt)) fr Lt

theorem genNorm_dOld_le {i : ℕ} {pc : ℤ} (j : Fin 2) (x : Gen .ctx i pc)
    (hl : leaf (Gen.dOld j x) = none) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (Gen.dOld j x) a mres L t ≤
      tStep D κc Δ i (fun m' L' => genNorm D κc Δ a₀ leaf x a m' L' t) mres L := by
  simp only [genNorm, hl, Option.elim, tStep]
  refine add_le_add le_rfl ?_
  split_ifs
  · exact le_rfl
  · exact zero_le

theorem tStep_mono {i : ℕ} {T T' : ℝ → ℕ → ℝ≥0∞} (hT : ∀ m L, T m L ≤ T' m L) (mres : ℝ)
    (L : ℕ) : tStep D κc Δ i T mres L ≤ tStep D κc Δ i T' mres L := by
  unfold tStep
  refine add_le_add ?_ (mul_le_mul_right (hT _ _) _)
  split_ifs
  · exact mul_le_mul_right (hT _ _) _
  · exact le_rfl

variable {i : ℕ} {pc : ℤ}
  (hleaf : ∀ (s : GenSort) (p : ℤ) (e : Gen s i p), leaf e = none)
include hleaf

theorem genNorm_kExpr_le (k : ℤ) (x y : Fin 2) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (kExpr i pc k x y) a mres L t ≤ kBound κc a L := by
  rw [kExpr, genNorm_add_eq D κc Δ a₀ leaf (hleaf _ _ _), genNorm_mul_eq D κc Δ a₀ leaf
    (hleaf _ _ _), genNorm_mul_eq D κc Δ a₀ leaf (hleaf _ _ _)]
  have hg := fun fr Lt => genNorm_geo_le D κc Δ a₀ leaf (i := i) (pc := pc) fr Lt (hleaf _ _ _) a
    mres L t
  calc _ ≤ geoW κc a L * geoW κc a L + geoW κc a L * geoW κc a L :=
        add_le_add (mul_le_mul' (hg _ _) (hg _ _)) (mul_le_mul' (hg _ _) (hg _ _))
    _ = kBound κc a L := by unfold kBound; ring

/-- **The Piola factor.** -/
theorem genNorm_tExpr_le (k : ℤ) (a t : ℝ) :
    ∀ (I A : List (Fin 2)) (mres : ℝ) (L : ℕ),
      genNorm D κc Δ a₀ leaf (tExpr i pc k I A) a mres L t ≤
        tBound D κc Δ a i I.length A.length mres L
  | [], [], mres, L => by
    rw [tExpr]
    exact (genNorm_const_le (D := D) κc Δ a₀ leaf 1 (hleaf _ _ _) a mres L t).trans
      (by simp [tBound])
  | [], _ :: _, mres, L => by
    rw [tExpr]
    exact (genNorm_const_le (D := D) κc Δ a₀ leaf 0 (hleaf _ _ _) a mres L t).trans
      (by simp [tBound])
  | j :: I, [], mres, L => by
    have ih := genNorm_tExpr_le k a t I []
    have hK := genNorm_kExpr_le D κc Δ a₀ leaf (pc := pc) hleaf k
    rw [tExpr, genNorm_add_eq D κc Δ a₀ leaf (hleaf _ _ _),
      genNorm_add_eq D κc Δ a₀ leaf (hleaf _ _ _), genNorm_mul_eq D κc Δ a₀ leaf (hleaf _ _ _),
      genNorm_mul_eq D κc Δ a₀ leaf (hleaf _ _ _)]
    have h0 := genNorm_const_le (D := D) κc Δ a₀ leaf (s := .ctx) (i := i) (p := pc) 0
      (hleaf _ _ _) a mres L t
    simp only [abs_zero, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at h0
    rw [h0, add_zero]
    have hdb : ∀ b : Fin 2, genNorm D κc Δ a₀ leaf (Gen.dOld b (tExpr i pc k I [])) a mres L t ≤
        tStep D κc Δ i (tBound D κc Δ a i I.length 0) mres L := fun b =>
      (genNorm_dOld_le D κc Δ a₀ leaf b _ (hleaf _ _ _) a mres L t).trans
        (tStep_mono D κc Δ (fun m' L' => ih m' L') mres L)
    simp only [List.length_cons, List.length_nil, tBound]
    calc _ ≤ kBound κc a L * tStep D κc Δ i (tBound D κc Δ a i I.length 0) mres L +
          kBound κc a L * tStep D κc Δ i (tBound D κc Δ a i I.length 0) mres L :=
        add_le_add (mul_le_mul' (hK _ _ a mres L t) (hdb 0)) (mul_le_mul' (hK _ _ a mres L t) (hdb 1))
      _ = _ := by ring
  | j :: I, x :: A₀, mres, L => by
    have ih := genNorm_tExpr_le k a t I (x :: A₀)
    have ih' := genNorm_tExpr_le k a t I A₀
    have hK := genNorm_kExpr_le D κc Δ a₀ leaf (pc := pc) hleaf k
    rw [tExpr, genNorm_add_eq D κc Δ a₀ leaf (hleaf _ _ _),
      genNorm_add_eq D κc Δ a₀ leaf (hleaf _ _ _), genNorm_mul_eq D κc Δ a₀ leaf (hleaf _ _ _),
      genNorm_mul_eq D κc Δ a₀ leaf (hleaf _ _ _), genNorm_mul_eq D κc Δ a₀ leaf (hleaf _ _ _)]
    have hdb : ∀ b : Fin 2,
        genNorm D κc Δ a₀ leaf (Gen.dOld b (tExpr i pc k I (x :: A₀))) a mres L t ≤
        tStep D κc Δ i (tBound D κc Δ a i I.length (A₀.length + 1)) mres L := fun b =>
      (genNorm_dOld_le D κc Δ a₀ leaf b _ (hleaf _ _ _) a mres L t).trans
        (tStep_mono D κc Δ (fun m' L' => ih m' L') mres L)
    simp only [List.length_cons, tBound]
    calc _ ≤ kBound κc a L * tStep D κc Δ i (tBound D κc Δ a i I.length (A₀.length + 1)) mres L +
          kBound κc a L * tStep D κc Δ i (tBound D κc Δ a i I.length (A₀.length + 1)) mres L +
          kBound κc a L * tBound D κc Δ a i I.length A₀.length mres L :=
        add_le_add (add_le_add (mul_le_mul' (hK _ _ a mres L t) (hdb 0))
          (mul_le_mul' (hK _ _ a mres L t) (hdb 1))) (mul_le_mul' (hK _ _ a mres L t) (ih' mres L))
      _ = _ := by ring

end AVRegularity.Providers.CascadeInvariants
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the real constants of the ledger.** For finite, decaying carrier constants
(`MajOK bw κ`) and an outer rate `a < 6π bw`, the entries of `J⁻¹` on the fast weights up to `D_m`,
the child profile and the Cauchy constant have real bounds `K, W, C_old` (`majOK_consts`), and for
`3π bw < a` the ledger weight of the pointwise decay has a real bound `W_r` (`ledgerWeight_le`).
All of them depend only on `κ`, `bw`, `a`, `D_m` and `L_*`, not on the level or the data `D`. -/

open AVRegularity.Providers.Majorant

/-- **The real bounds of the carrier constants.** -/
theorem majOK_consts {bw : ℝ} {κ : MajConsts} (hκ : MajOK bw κ) {a : ℝ}
    (ha : a < 6 * Real.pi * bw) (Dm : ℕ) :
    ∃ K W Cold : ℝ, 0 ≤ K ∧ 0 ≤ W ∧ 0 ≤ Cold ∧
      (∀ L, L ≤ Dm → kBound κ a L ≤ ENNReal.ofReal K) ∧
      wsum a 0 κ.child ≤ ENNReal.ofReal W ∧ κ.Cold ≤ ENNReal.ofReal Cold := by
  obtain ⟨C, hg, -, hc, hCold, -⟩ := hκ
  have hXt : wsum a Dm (expProfile C (6 * Real.pi * bw)) < ⊤ := wsum_expProfile_lt_top ha Dm C
  have hYt : wsum a 0 (expProfile C (6 * Real.pi * bw)) < ⊤ := wsum_expProfile_lt_top ha 0 C
  refine ⟨2 * (wsum a Dm (expProfile C (6 * Real.pi * bw))).toReal ^ 2,
    (wsum a 0 (expProfile C (6 * Real.pi * bw))).toReal, κ.Cold.toReal, by positivity,
    ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, fun L hL => ?_, ?_,
    (ENNReal.ofReal_toReal hCold).ge⟩
  · have hgeo : geoW κ a L ≤ wsum a Dm (expProfile C (6 * Real.pi * bw)) :=
      iSup₂_le fun fr Lt => (wsum_mono fun h => hg fr Lt h).trans (wsum_mono_weight le_rfl hL _)
    unfold kBound
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hXt.ne, ENNReal.ofReal_ofNat]
    gcongr
  · exact (wsum_mono fun h => hc h).trans (ENNReal.ofReal_toReal hYt.ne).ge

/-- **The real bound of the ledger weight** of the pointwise decay at the outer rate `a > 3π bw`. -/
theorem ledgerWeight_le {bw a : ℝ} (ha : 3 * Real.pi * bw < a) (L : ℕ) :
    ∃ Wr : ℝ, 0 ≤ Wr ∧ wsum (3 * Real.pi * bw) L (expProfile 1 a) ≤ ENNReal.ofReal Wr :=
  ⟨(wsum (3 * Real.pi * bw) L (expProfile 1 a)).toReal, ENNReal.toReal_nonneg,
    (ENNReal.ofReal_toReal (wsum_expProfile_lt_top ha L 1).ne).ge⟩

end AVRegularity.Providers.CascadeInvariants
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the scale of the Piola factor.** If the entries of `J⁻¹` are bounded by `K` on the
fast weights used, the Cauchy constant by `C_old`, the wavelength `ε = ε_i ≤ 1` and the reserve
`mres + nΔ ≤ 2`, then the Piola factor with `|I| = n`, `|β| = r` is at most `c^n ε^{-(n-r)}`,
`c = 2K(C_old/Δ + 2π) + K + 1` (`tBound_le`): each of its `n − r` derivatives costs one inverse
wavelength, the factor `ε_{i}^{d'-d}` of the higher transfer. -/

open AVRegularity.Providers.Majorant

/-- The constant of the Piola factor. -/
def tConst (K Cold Δ : ℝ) : ℝ := 2 * K * (Cold / Δ + 2 * Real.pi) + K + 1

theorem tConst_nonneg {K Cold Δ : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ Cold) (hΔ : 0 < Δ) :
    0 ≤ tConst K Cold Δ := by
  unfold tConst
  have : 0 ≤ Cold / Δ := div_nonneg hC hΔ.le
  positivity

theorem one_le_tConst {K Cold Δ : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ Cold) (hΔ : 0 < Δ) :
    1 ≤ tConst K Cold Δ := by
  unfold tConst
  have : 0 ≤ Cold / Δ := div_nonneg hC hΔ.le
  have : 0 ≤ 2 * K * (Cold / Δ + 2 * Real.pi) := by positivity
  linarith

variable (D : OCData) (κc : MajConsts) {Δ : ℝ} {a : ℝ} {i : ℕ}

/-- The cost of one derivative step of a bounded Piola factor. -/
theorem tStep_le (hε0 : 0 < D.eps i) (hΔ : 0 < Δ) {Cold : ℝ} (hC0 : 0 ≤ Cold)
    (hCold : κc.Cold ≤ ENNReal.ofReal Cold) (T : ℝ → ℕ → ℝ≥0∞) (B : ℝ) (mres : ℝ) (L : ℕ)
    (hB : 0 ≤ B) (hm : mres + Δ ≤ 2) (h1 : T (mres + Δ) L ≤ ENNReal.ofReal B)
    (h2 : T mres (L + 1) ≤ ENNReal.ofReal B) :
    tStep D κc Δ i T mres L ≤ ENNReal.ofReal ((Cold / Δ + 2 * Real.pi) * (D.eps i)⁻¹ * B) := by
  unfold tStep
  simp only [hm, ↓reduceIte]
  have e1 : κc.Cold / ENNReal.ofReal (D.eps i * Δ) * T (mres + Δ) L ≤
      ENNReal.ofReal (Cold / Δ * (D.eps i)⁻¹ * B) := by
    calc κc.Cold / ENNReal.ofReal (D.eps i * Δ) * T (mres + Δ) L
        ≤ ENNReal.ofReal Cold / ENNReal.ofReal (D.eps i * Δ) * ENNReal.ofReal B :=
          mul_le_mul' (ENNReal.div_le_div_right hCold _) h1
      _ = ENNReal.ofReal (Cold / Δ * (D.eps i)⁻¹ * B) := by
          rw [← ENNReal.ofReal_div_of_pos (mul_pos hε0 hΔ), ← ENNReal.ofReal_mul
            (div_nonneg hC0 (mul_pos hε0 hΔ).le)]
          congr 1
          field_simp
  have e2 : ENNReal.ofReal (2 * Real.pi / D.eps i) * T mres (L + 1) ≤
      ENNReal.ofReal (2 * Real.pi * (D.eps i)⁻¹ * B) := by
    calc ENNReal.ofReal (2 * Real.pi / D.eps i) * T mres (L + 1)
        ≤ ENNReal.ofReal (2 * Real.pi / D.eps i) * ENNReal.ofReal B := mul_le_mul_right h2 _
      _ = ENNReal.ofReal (2 * Real.pi * (D.eps i)⁻¹ * B) := by
          rw [← ENNReal.ofReal_mul (div_nonneg (by positivity) hε0.le), div_eq_mul_inv]
  calc _ ≤ ENNReal.ofReal (Cold / Δ * (D.eps i)⁻¹ * B) +
        ENNReal.ofReal (2 * Real.pi * (D.eps i)⁻¹ * B) := add_le_add e1 e2
    _ = ENNReal.ofReal ((Cold / Δ + 2 * Real.pi) * (D.eps i)⁻¹ * B) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The scale of the Piola factor.** Within the reserve, the Piola factor vanishes when the
word `β` is longer than `I`, and is at most `c^n ε^{-(n-r)}` otherwise. -/
theorem tBound_le (hε0 : 0 < D.eps i) (hε1 : D.eps i ≤ 1) (hΔ : 0 < Δ) {Cold K : ℝ}
    (hC0 : 0 ≤ Cold) (hK0 : 0 ≤ K) (hCold : κc.Cold ≤ ENNReal.ofReal Cold) {L₀ : ℕ}
    (hK : ∀ L, L ≤ L₀ → kBound κc a L ≤ ENNReal.ofReal K) :
    ∀ (n r : ℕ) (mres : ℝ) (L : ℕ), mres + n * Δ ≤ 2 → L + n ≤ L₀ →
      (n < r → tBound D κc Δ a i n r mres L = 0) ∧
      (r ≤ n → tBound D κc Δ a i n r mres L ≤
        ENNReal.ofReal (tConst K Cold Δ ^ n * (D.eps i)⁻¹ ^ (n - r))) := by
  set c := tConst K Cold Δ with hc
  have hc0 : 0 ≤ c := tConst_nonneg hK0 hC0 hΔ
  have hεi : 1 ≤ (D.eps i)⁻¹ := one_le_inv₀ hε0 |>.mpr hε1
  have hcoef : 2 * K * (Cold / Δ + 2 * Real.pi) + K ≤ c := by rw [hc]; unfold tConst; linarith
  have hcoef0 : 0 ≤ 2 * K * (Cold / Δ + 2 * Real.pi) := by
    have : 0 ≤ Cold / Δ := div_nonneg hC0 hΔ.le
    positivity
  intro n
  induction n with
  | zero =>
    intro r mres L _ _
    refine ⟨fun hr => ?_, fun hr => ?_⟩
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simp [tBound]
    · obtain rfl : r = 0 := by omega
      simp [tBound]
  | succ n ih =>
    intro r mres L hm hL
    have hn0 : (0 : ℝ) ≤ n * Δ := by positivity
    have hm' : mres + Δ + n * Δ ≤ 2 := by push_cast at hm; linarith
    have hm0 : mres + n * Δ ≤ 2 := by push_cast at hm; linarith
    have hmΔ : mres + Δ ≤ 2 := by push_cast at hm; linarith
    have hKL : kBound κc a L ≤ ENNReal.ofReal K := hK L (by omega)
    have ihA := fun r => ih r (mres + Δ) L hm' (by omega)
    have ihB := fun r => ih r mres (L + 1) hm0 (by omega)
    have ihC := fun r => ih r mres L hm0 (by omega)
    -- a vanishing step
    have hstep0 : ∀ r, n < r → tStep D κc Δ i (tBound D κc Δ a i n r) mres L = 0 := by
      intro r hr
      unfold tStep
      simp only [hmΔ, ↓reduceIte, (ihA r).1 hr, (ihB r).1 hr, mul_zero, add_zero]
    refine ⟨fun hr => ?_, fun hr => ?_⟩
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simp only [tBound, hstep0 (r' + 1) (by omega), (ihC r').1 (by omega), mul_zero, add_zero]
    · cases r with
      | zero =>
        simp only [tBound]
        have hT := tStep_le D κc hε0 hΔ hC0 hCold (tBound D κc Δ a i n 0)
          (c ^ n * (D.eps i)⁻¹ ^ (n - 0)) mres L (by positivity) hmΔ ((ihA 0).2 (by omega))
          ((ihB 0).2 (by omega))
        calc 2 * kBound κc a L * tStep D κc Δ i (tBound D κc Δ a i n 0) mres L
            ≤ 2 * ENNReal.ofReal K * ENNReal.ofReal ((Cold / Δ + 2 * Real.pi) * (D.eps i)⁻¹ *
                (c ^ n * (D.eps i)⁻¹ ^ (n - 0))) :=
              mul_le_mul' (mul_le_mul_right hKL _) hT
          _ = ENNReal.ofReal (2 * K * (Cold / Δ + 2 * Real.pi) * (c ^ n * (D.eps i)⁻¹ ^ (n + 1))) := by
              rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
                ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [Nat.sub_zero, pow_succ ((D.eps i)⁻¹) n]
              ring
          _ ≤ ENNReal.ofReal (c ^ (n + 1) * (D.eps i)⁻¹ ^ (n + 1 - 0)) := by
              apply ENNReal.ofReal_le_ofReal
              rw [Nat.sub_zero, pow_succ c n]
              have hX : 0 ≤ c ^ n * (D.eps i)⁻¹ ^ (n + 1) := by positivity
              calc 2 * K * (Cold / Δ + 2 * Real.pi) * (c ^ n * (D.eps i)⁻¹ ^ (n + 1))
                  ≤ c * (c ^ n * (D.eps i)⁻¹ ^ (n + 1)) :=
                    mul_le_mul_of_nonneg_right (by linarith) hX
                _ = c ^ n * c * (D.eps i)⁻¹ ^ (n + 1) := by ring
      | succ r =>
        simp only [tBound]
        have hTC := (ihC r).2 (by omega)
        -- the derivative term
        have hD : 2 * kBound κc a L * tStep D κc Δ i (tBound D κc Δ a i n (r + 1)) mres L ≤
            ENNReal.ofReal (2 * K * (Cold / Δ + 2 * Real.pi) *
              (c ^ n * (D.eps i)⁻¹ ^ (n + 1 - (r + 1)))) := by
          by_cases hrn : r + 1 ≤ n
          · have hT := tStep_le D κc hε0 hΔ hC0 hCold (tBound D κc Δ a i n (r + 1))
              (c ^ n * (D.eps i)⁻¹ ^ (n - (r + 1))) mres L (by positivity) hmΔ
              ((ihA (r + 1)).2 hrn) ((ihB (r + 1)).2 hrn)
            calc 2 * kBound κc a L * tStep D κc Δ i (tBound D κc Δ a i n (r + 1)) mres L
                ≤ 2 * ENNReal.ofReal K * ENNReal.ofReal ((Cold / Δ + 2 * Real.pi) * (D.eps i)⁻¹ *
                    (c ^ n * (D.eps i)⁻¹ ^ (n - (r + 1)))) :=
                  mul_le_mul' (mul_le_mul_right hKL _) hT
              _ = ENNReal.ofReal (2 * K * (Cold / Δ + 2 * Real.pi) *
                    (c ^ n * (D.eps i)⁻¹ ^ (n + 1 - (r + 1)))) := by
                  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
                    ← ENNReal.ofReal_mul (by positivity)]
                  congr 1
                  have he : n + 1 - (r + 1) = (n - (r + 1)) + 1 := by omega
                  rw [he, pow_succ ((D.eps i)⁻¹)]
                  ring
          · rw [hstep0 (r + 1) (by omega), mul_zero]
            exact zero_le
        have hX : 0 ≤ c ^ n * (D.eps i)⁻¹ ^ (n + 1 - (r + 1)) := by positivity
        have hp : (D.eps i)⁻¹ ^ (n - r) = (D.eps i)⁻¹ ^ (n + 1 - (r + 1)) := by
          congr 1
          omega
        calc 2 * kBound κc a L * tStep D κc Δ i (tBound D κc Δ a i n (r + 1)) mres L +
              kBound κc a L * tBound D κc Δ a i n r mres L
            ≤ ENNReal.ofReal (2 * K * (Cold / Δ + 2 * Real.pi) *
                (c ^ n * (D.eps i)⁻¹ ^ (n + 1 - (r + 1)))) +
              ENNReal.ofReal K * ENNReal.ofReal (c ^ n * (D.eps i)⁻¹ ^ (n - r)) :=
              add_le_add hD (mul_le_mul' hKL hTC)
          _ = ENNReal.ofReal ((2 * K * (Cold / Δ + 2 * Real.pi) + K) *
                (c ^ n * (D.eps i)⁻¹ ^ (n + 1 - (r + 1)))) := by
              rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_add (by positivity) (by positivity), hp]
              congr 1
              ring
          _ ≤ ENNReal.ofReal (c ^ (n + 1) * (D.eps i)⁻¹ ^ (n + 1 - (r + 1))) := by
              apply ENNReal.ofReal_le_ofReal
              calc (2 * K * (Cold / Δ + 2 * Real.pi) + K) *
                    (c ^ n * (D.eps i)⁻¹ ^ (n + 1 - (r + 1)))
                  ≤ c * (c ^ n * (D.eps i)⁻¹ ^ (n + 1 - (r + 1))) :=
                    mul_le_mul_of_nonneg_right hcoef hX
                _ = c ^ (n + 1) * (D.eps i)⁻¹ ^ (n + 1 - (r + 1)) := by ring

end AVRegularity.Providers.CascadeInvariants
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the structural norm of the explicit transfer at a fixed time.** One summand
`J⁻¹ · ϖ_k c_k(𝒜^♮) · T_{I,β}` costs `ϖ_{i+1,k}(t)` times `K · W_child · ‖c_k‖ · T_{|I|,|β|}`
(`genNorm_transferTerm_le`), and the sum over the finer slots is a sub-convex combination of the
cutoff weights (`genNorm_transferExpr_le`): the explicit transfer costs `|C|` times any common bound
of the finer slots' sums. This is the source's "at each time, a convex combination over
`p ≺ p̃`". -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable (D : OCData) (κc : MajConsts) (Δ a₀ : ℝ)
  (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞))

/-- The structural norm of an explicit finite sum is at most the sum of the norms. -/
theorem genNorm_genSumFinset_le {s : GenSort} {i : ℕ} {p : ℤ} {ι : Type*}
    (hadd : ∀ x y : Gen s i p, leaf (Gen.add x y) = none)
    (h0 : leaf (Gen.time (s := s) (i := i) (p := p) (.const 0)) = none) (a mres : ℝ) (L : ℕ)
    (t : ℝ) (S : Finset ι) (f : ι → Gen s i p) :
    genNorm D κc Δ a₀ leaf (genSumList (S.toList.map f)) a mres L t ≤
      ∑ x ∈ S, genNorm D κc Δ a₀ leaf (f x) a mres L t := by
  refine (genNorm_genSumList_le (D := D) κc Δ a₀ leaf hadd h0 a mres L t _).trans (le_of_eq ?_)
  rw [List.map_map, Finset.sum_map_toList]
  rfl

variable {i : ℕ} {pc : ℤ}
  (hleaf : ∀ (s : GenSort) (p : ℤ) (e : Gen s i p), leaf e = none)
include hleaf

/-- **One summand of the transfer.** -/
theorem genNorm_transferTerm_le (k : ℤ) (κ : Fin 2) {d : ℕ} (I : DerivativeWord2 (d - 1))
    (i₀ : Fin 2) {d' : ℕ} (β : DerivativeWord2 (d' - 1)) (c : Gen .fam (i + 1) k) (a mres : ℝ)
    (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (transferTerm i pc k κ I i₀ β c) a mres L t ≤
      ENNReal.ofReal (ocCutoff D.α D.q D.Λ (i + 1) k t) *
        (kBound κc a L * wsum a L κc.child * genNorm D κc Δ a₀ leaf c a₀ mres 0 t *
          tBound D κc Δ a i (d - 1) (d' - 1) mres L) := by
  rw [transferTerm, genNorm_mul_eq D κc Δ a₀ leaf (hleaf _ _ _),
    genNorm_mul_eq D κc Δ a₀ leaf (hleaf _ _ _), genNorm_evalChild_eq D κc Δ a₀ leaf (hleaf _ _ _)]
  have hK := genNorm_kExpr_le D κc Δ a₀ leaf (pc := pc) hleaf k κ i₀ a mres L t
  have hT := genNorm_tExpr_le D κc Δ a₀ leaf (pc := pc) hleaf k a t (List.ofFn I) (List.ofFn β)
    mres L
  rw [List.length_ofFn, List.length_ofFn] at hT
  calc _ ≤ kBound κc a L * (ENNReal.ofReal (ocCutoff D.α D.q D.Λ (i + 1) k t) *
          wsum a L κc.child * genNorm D κc Δ a₀ leaf c a₀ mres 0 t) *
          tBound D κc Δ a i (d - 1) (d' - 1) mres L :=
        mul_le_mul' (mul_le_mul' hK le_rfl) hT
    _ = _ := by ring

/-- **The explicit transfer at a fixed time**: a sub-convex combination over the finer slots. -/
theorem genNorm_transferExpr_le (hτ : 0 < ocTau D.α D.q D.Λ (i + 1)) (C : ℝ) (S : Finset ℤ)
    (hS : ∀ k ∈ S, Odd k) (Dγ d' : ℕ) (β : DerivativeWord2 (d' - 1)) (κ : Fin 2)
    (c : (k : ℤ) → (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Gen .fam (i + 1) k)
    (a mres : ℝ) (L : ℕ) (t : ℝ) (Y : ℝ≥0∞)
    (hY : ∀ k ∈ S, ∑ d ∈ Finset.Icc (d' - 1 + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2,
      kBound κc a L * wsum a L κc.child * genNorm D κc Δ a₀ leaf (c k d I i₀) a₀ mres 0 t *
        tBound D κc Δ a i (d - 1) (d' - 1) mres L ≤ Y) :
    genNorm D κc Δ a₀ leaf (transferExpr i pc C S Dγ d' β κ c) a mres L t ≤
      ENNReal.ofReal |C| * Y := by
  have hadd : ∀ x y : Gen .ctx i pc, leaf (Gen.add x y) = none := fun _ _ => hleaf _ _ _
  rw [transferExpr, genNorm_mul_eq D κc Δ a₀ leaf (hleaf _ _ _)]
  refine mul_le_mul' (genNorm_const_le (D := D) κc Δ a₀ leaf C (hleaf _ _ _) a mres L t) ?_
  refine (genNorm_genSumFinset_le D κc Δ a₀ leaf hadd (hleaf _ _ _) a mres L t S _).trans ?_
  have hconv := sum_ocCutoff_mul_le hτ S hS t (fun k => ∑ d ∈ Finset.Icc (d' - 1 + 1) Dγ,
    ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2,
      kBound κc a L * wsum a L κc.child * genNorm D κc Δ a₀ leaf (c k d I i₀) a₀ mres 0 t *
        tBound D κc Δ a i (d - 1) (d' - 1) mres L) hY
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) hconv
  refine (genNorm_genSumFinset_le D κc Δ a₀ leaf hadd (hleaf _ _ _) a mres L t _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  refine (genNorm_genSumFinset_le D κc Δ a₀ leaf hadd (hleaf _ _ _) a mres L t _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun I _ => ?_
  refine (genNorm_genSumFinset_le D κc Δ a₀ leaf hadd (hleaf _ _ _) a mres L t _ _).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i₀ _ =>
    genNorm_transferTerm_le D κc Δ a₀ leaf hleaf k κ I i₀ β (c k d I i₀) a mres L t

end AVRegularity.Providers.CascadeInvariants
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the explicit direct transport.** Given explicit expressions `oldE` of the old
coefficients (one per slot, edge, order, word and component), the entry
`fluxCoeff (directFlux G p cc γ ords t) d I 0 κ` is denoted by the explicit family expression
`c_d · Σ_σ mean (restrict (oldE p γ d (I∘σ) κ))`, `c_d = κ_m ε_m^{d-2}/(d-1)!` for `d ∈ ords` and
`0` otherwise (`directExpr`, `famURep_directExpr`; `directFlux_famRep` with the sums and
the old expressions made explicit). Its structural norm is at most `|c_d|` times the sum of the
norms of the old expressions, read at the inner rate (`genNorm_directExpr_le`): every new node is
a family or cell node, never a certified leaf. -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem FamURep.genSumFinset {Λ : Type} {V : UEnv Λ} {κ : Type*} (s : Finset κ)
    (ψ : κ → Λ → ℝ) (f : κ → Gen .fam V.E.i V.E.p) (h : ∀ k ∈ s, V.FamURep (ψ k) (f k)) :
    V.FamURep (fun l => ∑ k ∈ s, ψ k l) (CascadeInvariants.genSumList (s.toList.map f)) := by
  have hl : ∀ l : List κ, (∀ k ∈ l, V.FamURep (ψ k) (f k)) →
      V.FamURep (fun x => (l.map fun k => ψ k x).sum) (CascadeInvariants.genSumList (l.map f)) := by
    intro l
    induction l with
    | nil => exact fun _ => (UEnv.famURep_const V 0).congr fun _ _ => by simp
    | cons a l ih =>
      intro h'
      exact ((h' a List.mem_cons_self).add (ih fun k hk => h' k (List.mem_cons_of_mem a hk))).congr
        fun _ _ => by simp
  exact (hl s.toList fun k hk => h k (Finset.mem_toList.mp hk)).congr
    fun _ _ => (Finset.sum_map_toList s _).symm

/-- The coefficient of the order-`d` direct term. -/
def directConst (D : OCData) (m : ℕ) (ords : Finset ℕ) (d : ℕ) : ℝ :=
  if d ∈ ords then D.kap m * D.eps m ^ (d - 2) * ((d - 1).factorial : ℝ)⁻¹ else 0

/-- **The explicit direct-transport expression.** -/
def directExpr (m : ℕ) (k : ℤ) (C : ℝ) {d : ℕ} (I : DerivativeWord2 (d - 1)) (κ : Fin 2)
    (oldE : DerivativeWord2 (d - 1) → Fin 2 → Gen .ctx m k) : Gen .fam m k :=
  Gen.mul (Gen.time (.const C))
    (genSumList ((Finset.univ : Finset (Equiv.Perm (Fin (d - 1)))).toList.map
      fun σ : Equiv.Perm (Fin (d - 1)) => Gen.mean (Gen.restrict (oldE (I ∘ ⇑σ) κ))))

open scoped Classical in
theorem famURep_directExpr (hζ : IsFastProfile D.ζ) (G : GenStage D hr Dm b j₀) (p : OddSlot)
    {v u : CompIn G.comps} (γ : G.fam.Γ v u) (ords : Finset ℕ) (hords : ∀ d' ∈ ords, 1 ≤ d')
    {d : ℕ} (hd : 1 ≤ d) (I : DerivativeWord2 (d - 1)) (κ : Fin 2)
    (oldE : DerivativeWord2 (d - 1) → Fin 2 → Gen .ctx G.level p.1)
    (hold : ∀ (J : DerivativeWord2 (d - 1)) (c : Fin 2), Gen.IsScheduled D (oldE J c) ∧
      Gen.FromSeed G.exports (oldE J c) ∧ ∃ f : GenSort.Sem .ctx, Gen.Denotes D b j₀ (oldE J c) f ∧
        ∀ (cc : StageCtx D b j₀ G.level p) (t : ℝ), t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 →
          ∀ (X z : Vec 2), G.fam.flux p cc v u γ d J t X z c =
            if IsAdmissibleChain D b j₀ G.level p.1 (cc.1.recenter D (D.eps (G.level - 1) • X))
            then f t (cc.1.recenter D (D.eps (G.level - 1) • X)) z else 0)
    (hint : d ∈ ords → ∀ (c : StageCtx D b j₀ G.level p),
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1, ∀ σ : Equiv.Perm (Fin (d - 1)),
        IntegrableOn (fun z => G.fam.flux p c v u γ d (I ∘ σ) t 0 z) AVenhance.unitCube) :
    (directEnv G p).FamURep (fun l => fluxCoeff (directFlux G p l.1 γ ords l.2) d I 0 κ)
      (directExpr G.level p.1 (directConst D G.level ords d) I κ oldE) := by
  classical
  set V := directEnv G p with hV
  have hone : ∀ σ : Equiv.Perm (Fin (d - 1)), V.FamURep (fun l => ∫ z in AVenhance.unitCube,
      G.fam.flux p l.1 v u γ d (I ∘ σ) l.2 0 z κ) (Gen.mean (Gen.restrict (oldE (I ∘ σ) κ))) := by
    intro σ
    obtain ⟨hs, hf, f, hden, hfl⟩ := hold (I ∘ σ) κ
    refine UEnv.famURep_meanRestrict hs hf hden fun l hl => ?_
    have hz : ∀ z, G.fam.flux p l.1 v u γ d (I ∘ σ) l.2 0 z κ = f l.2 l.1.1 z := fun z => by
      rw [hfl l.1 l.2 hl 0 z]
      simp only [smul_zero, recenter_zero D hζ, l.1.2, ↓reduceIte]
    simp only [hz]
    rfl
  have hsum := FamURep.genSumFinset (V := V) (Finset.univ : Finset (Equiv.Perm (Fin (d - 1))))
    (fun σ l => ∫ z in AVenhance.unitCube, G.fam.flux p l.1 v u γ d (I ∘ σ) l.2 0 z κ)
    (fun σ : Equiv.Perm (Fin (d - 1)) => Gen.mean (Gen.restrict (oldE (I ∘ ⇑σ) κ)))
    fun σ _ => hone σ
  refine ((UEnv.famURep_const V (directConst D G.level ords d)).mul hsum).congr fun l hl => ?_
  have h1 := congrFun (fluxCoeff_directFlux G p l.1 γ ords hords l.2 hd I) κ
  rw [h1]
  by_cases hdo : d ∈ ords
  · simp only [directConst, hdo, ↓reduceIte, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun σ _ => fieldCellMean_apply (hint hdo l.1 l.2 hl σ) κ
  · simp [directConst, hdo]

variable (κc : MajConsts) (Δ a₀ : ℝ)
  (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞))

/-- **The structural norm of the direct transport** (for leaf maps without family or cell
leaves, e.g. certified ones, `LeavesCertified.1`). -/
theorem genNorm_directExpr_le
    (hL : ∀ (s : GenSort) (i : ℕ) (p : ℤ) (e : Gen s i p), s ≠ .ctx → leaf e = none)
    (m : ℕ) (k : ℤ) (C : ℝ) {d : ℕ}
    (I : DerivativeWord2 (d - 1)) (κ : Fin 2) (oldE : DerivativeWord2 (d - 1) → Fin 2 → Gen .ctx m k)
    (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (directExpr m k C I κ oldE) a mres L t ≤
      ENNReal.ofReal |C| * ∑ σ : Equiv.Perm (Fin (d - 1)),
        genNorm D κc Δ a₀ leaf (oldE (I ∘ σ) κ) a₀ mres 0 t := by
  have hn : ∀ (i : ℕ) (p : ℤ) (e : Gen .fam i p), leaf e = none := fun i p e =>
    hL .fam i p e (by intro h; cases h)
  have hnc : ∀ (i : ℕ) (p : ℤ) (e : Gen .cell i p), leaf e = none := fun i p e =>
    hL .cell i p e (by intro h; cases h)
  rw [directExpr, genNorm_mul_eq D κc Δ a₀ leaf (hn _ _ _)]
  refine mul_le_mul' (genNorm_const_le (D := D) κc Δ a₀ leaf C (hn _ _ _) a mres L t) ?_
  refine (genNorm_genSumList_le (D := D) κc Δ a₀ leaf (fun x y => hn _ _ _) (hn _ _ _) a mres L
    t _).trans (le_of_eq ?_)
  rw [List.map_map, Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Function.comp_apply, genNorm, hn, hnc, Option.elim]

end AVRegularity.Providers.CascadeInvariants
end
end

section
@[expose] public section
open AVRegularity.Sobolev
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the record arithmetic of the direct transport.** The direct term of order `d₁` of
an old identity of length `ℓ` has the coefficient `κ_{i+1} ε_{i+1}^{d₁-2}/(d₁-1)!` times the sum of
the old coefficients over the permuted words (`sum_perm_comp`: the permutations cost `(d₁-1)!`).
Transferred to the order `d ≤ d₁` at the coarse level `i`, normalized by `(κ_i ε_i^{d-2})⁻¹` and
with the Piola factor `c^{d₁-1} ε_i^{-(d₁-d)}`, it has tagged size at most `c^{d₁-1}` times the old
record size, given the old record bound `(ε_{i+1}/ℓ)^{d₁-2} Σθ_old ≤ S`, `ℓ ≤ ε_i` and
`κ_{i+1} ≤ κ_i` (`dirTerm_le`): the source's `C(κ_i/B)(ρ_b/E)^{d-d'}θ`. -/

/-- **The permutations of a derivative word cost `(n)!`.** -/
theorem sum_perm_comp (n : ℕ) (f : DerivativeWord2 n → Fin 2 → ℝ) :
    ∑ I : DerivativeWord2 n, ∑ i₀ : Fin 2, ∑ σ : Equiv.Perm (Fin n), f (I ∘ σ) i₀ =
      (n.factorial : ℝ) * ∑ J : DerivativeWord2 n, ∑ i₀ : Fin 2, f J i₀ := by
  have h1 : ∀ σ : Equiv.Perm (Fin n), ∑ I : DerivativeWord2 n, ∑ i₀ : Fin 2, f (I ∘ σ) i₀ =
      ∑ J : DerivativeWord2 n, ∑ i₀ : Fin 2, f J i₀ := fun σ =>
    Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Fin 2))) fun J => ∑ i₀ : Fin 2, f J i₀
  calc ∑ I : DerivativeWord2 n, ∑ i₀ : Fin 2, ∑ σ : Equiv.Perm (Fin n), f (I ∘ σ) i₀
      = ∑ I : DerivativeWord2 n, ∑ σ : Equiv.Perm (Fin n), ∑ i₀ : Fin 2, f (I ∘ σ) i₀ :=
        Finset.sum_congr rfl fun I _ => Finset.sum_comm
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ I : DerivativeWord2 n, ∑ i₀ : Fin 2, f (I ∘ σ) i₀ :=
        Finset.sum_comm
    _ = ∑ _σ : Equiv.Perm (Fin n), ∑ J : DerivativeWord2 n, ∑ i₀ : Fin 2, f J i₀ :=
        Finset.sum_congr rfl fun σ _ => h1 σ
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- **One direct order transferred, against the old record.** With `k = d - 2` and
`k + j = d₁ - 2`: `(E/ℓ)^k (κ E^k)⁻¹ · κ' e^{k+j} · c^{n} E^{-j} · Σθ ≤ c^n S` whenever
`(e/ℓ)^{k+j} Σθ ≤ S`, `ℓ ≤ E` and `κ' ≤ κ`. -/
theorem dirTerm_le {E e ℓ κ κ' c S sθ : ℝ} (hE : 0 < E) (he : 0 < e) (hℓ : 0 < ℓ) (hℓE : ℓ ≤ E)
    (hκ : 0 < κ) (hκ' : 0 ≤ κ') (hκκ : κ' ≤ κ) (hc : 0 ≤ c) (hsθ : 0 ≤ sθ) (k j n : ℕ)
    (hθ : (e / ℓ) ^ (k + j) * sθ ≤ S) :
    (E / ℓ) ^ k * |(κ * E ^ k)⁻¹| * (κ' * e ^ (k + j) * (c ^ n * E⁻¹ ^ j) * sθ) ≤ c ^ n * S := by
  have hEk : 0 < κ * E ^ k := by positivity
  rw [abs_of_pos (inv_pos.mpr hEk)]
  have key : (E / ℓ) ^ k * (κ * E ^ k)⁻¹ * (κ' * e ^ (k + j) * (c ^ n * E⁻¹ ^ j) * sθ) =
      κ' / κ * (ℓ / E) ^ j * c ^ n * ((e / ℓ) ^ (k + j) * sθ) := by
    have hEc : E ^ k * E⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hE.ne', one_pow]
    have hℓc : ℓ ^ j * ℓ⁻¹ ^ j = 1 := by rw [← mul_pow, mul_inv_cancel₀ hℓ.ne', one_pow]
    linear_combination (ℓ⁻¹ ^ k * κ⁻¹ * κ' * e ^ (k + j) * c ^ n * E⁻¹ ^ j * sθ) * hEc -
      (ℓ⁻¹ ^ k * κ⁻¹ * κ' * e ^ (k + j) * c ^ n * E⁻¹ ^ j * sθ) * hℓc
  rw [key]
  have h1 : κ' / κ ≤ 1 := (div_le_one hκ).mpr hκκ
  have h2 : (ℓ / E) ^ j ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hE).mpr hℓE)
  have hS : 0 ≤ (e / ℓ) ^ (k + j) * sθ := by positivity
  have h0 : 0 ≤ κ' / κ := div_nonneg hκ' hκ.le
  have hp : 0 ≤ (ℓ / E) ^ j := by positivity
  have hcn : 0 ≤ c ^ n := pow_nonneg hc n
  have h12 : κ' / κ * (ℓ / E) ^ j ≤ 1 * 1 := mul_le_mul h1 h2 hp zero_le_one
  calc κ' / κ * (ℓ / E) ^ j * c ^ n * ((e / ℓ) ^ (k + j) * sθ)
      ≤ 1 * 1 * c ^ n * S :=
        mul_le_mul (mul_le_mul_of_nonneg_right h12 hcn) hθ hS
          (by rw [one_mul, one_mul]; exact hcn)
    _ = c ^ n * S := by ring

end AVRegularity.Providers.CascadeInvariants
end
end
