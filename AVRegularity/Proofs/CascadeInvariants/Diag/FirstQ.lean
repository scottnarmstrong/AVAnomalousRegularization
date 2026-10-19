-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.CascadeInvariants.Diag.BridgeJet
public import AVRegularity.Proofs.CascadeInvariants.Jet.CovLetter
public import AVRegularity.Proofs.GenSem.Jet.CtxChart
public import AVRegularity.Proofs.CascadeInvariants.Diag.ArrQOps
import AVRegularity.Proofs.GenSem.First.RepMain
import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Proofs.GenSem.Jet.Chart
import AVRegularity.Proofs.GenSem.LiftOn.Omega
import AVRegularity.Proofs.GenSem.Op.FamChart

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology Homogenization AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, first source: sized jets of the bridge arrays of an appended child.** On the good
pairs (a time of the lift window, a family of the grade-zero setup), the point-jets of
`x ↦ hSem(A^{[Ψ⁻¹x]})`, which are the jets of the bridge arrays of the appended child
(`ChildLift.bridgeChild_eq_hSem`), are sized family functions with carrier-calculus invariants
(`jetRepGQ_bridge`): the push-forward tensor has the small size `16 C_Ŝ` (`famInv_hSem`), its
covariant jets cost the slow factor `σ`, and the inverse centered map is composed by the sized
chain rule (`jetRepGQ_dLabel_famMapInv_of`, generic in the sized algebra). -/

section
open AVRegularity.Providers.ComplexContext AVRegularity.Providers.ComplexFlow AVRegularity.Providers.GenSem

/-! ### The inverse centered map, for any sized algebra -/

section Generic

variable {Λ : Type*} {R : (Λ → ℝ) → ℕ → ℝ≥0 → Prop} {σ : ℝ≥0}

/-- **Jets of the inverse centered map** from sized jets of the inverse Jacobian letters. -/
theorem jetRepGQ_dLabel_famMapInv_of (hR : RepAlgQ R) {D : OCData} (hζ : IsFastProfile D.ζ)
    (π : Λ → ℝ × RealChain) (hW : ∀ l, (π l).2.WellSlotted) {K : ℝ≥0}
    (hG : ∀ n b j, JetRepGQ R σ n
      (fun l w => (((π l).2.recenter D w).famJac D (π l).1)⁻¹ b j) 0 K) :
    ∀ (n : ℕ) (b j : Fin 2), JetRepGQ R σ n
      (dLabelG j (fun l x => (π l).2.famMapInv D (π l).1 x b)) 0 (invP K n) := by
  have heq : ∀ b j, dLabelG j (fun l x => (π l).2.famMapInv D (π l).1 x b) =
      fun l x => (fun l w => (((π l).2.recenter D w).famJac D (π l).1)⁻¹ b j) l
        ((π l).2.famMapInv D (π l).1 x) := by
    intro b j
    funext l x
    simp only [dLabelG]
    exact dLabel_famMapInv hζ (π l).2 (hW l) (π l).1 b j x
  intro n
  induction n with
  | zero =>
    intro b j
    rw [heq b j]
    have e : (fun l => (fun l w => (((π l).2.recenter D w).famJac D (π l).1)⁻¹ b j) l
        ((π l).2.famMapInv D (π l).1 0)) =
        fun l => (fun l w => (((π l).2.recenter D w).famJac D (π l).1)⁻¹ b j) l 0 :=
      funext fun l => by rw [famMapInv_zero hζ]
    show R _ 0 (invP K 0)
    rw [e]
    exact (hG 0 b j).value
  | succ n ih =>
    intro b j
    rw [heq b j]
    exact JetRepGQ.comp' hR (fun l => famMapInv_zero hζ (π l).2 (π l).1)
      (fun l => (contDiff_famJacInv hζ (π l).2 (hW l) (π l).1 b j).of_le
        (by exact_mod_cast le_top))
      (fun l => (contDiff_famMapInv (π l).2 (π l).1).of_le (by exact_mod_cast le_top))
      (hG (n + 1) b j)
      (fun b' j' => (ih b' j').mono hR le_rfl (Nat.zero_le _) le_rfl)

end Generic

/-! ### The push-forward tensor -/

theorem famInvQ_congr {D : OCData} {b : ℝ} {j₀ m : ℕ} {k : ℤ} {Δ μ₀ : ℝ} {Λ : Type*}
    {π : Λ → ℝ × RealChain} {F F' : Λ → ℝ} {r : ℕ} {C : ℝ≥0}
    (hF : famInvQ D b j₀ m k Δ μ₀ π F r C) (h : ∀ l, F l = F' l) :
    famInvQ D b j₀ m k Δ μ₀ π F' r C := by
  obtain ⟨f, G, hf, hI⟩ := hF
  exact ⟨f, G, fun l => (h l).symm.trans (hf l), hI⟩

variable {D : OCData} {b : ℝ} {j₀ m : ℕ} {k : ℤ} {CH Υ : ℝ} {Δ μ₀ : ℝ} {Cd : ℝ}

/-- The size `C_Ŝ = 14(C_d² + 1) κ_{m−1} ownSize(m)` of the label tensor. -/
def sizeS (D : OCData) (m : ℕ) (Cd : ℝ) : ℝ≥0 :=
  Real.toNNReal (14 * (Cd ^ 2 + 1) * D.kap (m - 1) * ownSize D m)

/-- **The family invariant of the push-forward tensor**, of size `16 C_Ŝ`. -/
theorem famInv_hSem (env : ChainEnv D b CH Υ j₀) (hm : ownSize D m ≤ 1 / 100)
    (hκ : ∀ i, 0 < D.kap i) (hk : Odd k)
    (hCd : D.eps m ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap m * D.kap (m - 1)))
    (hc : 0 < D.cellScaleSq m) (hκm : D.kap m = D.κ m) (hκle : D.kap m ≤ D.kap (m - 1))
    (hΔ : 0 ≤ Δ) (c g : Fin 2) :
    ∃ G : Ext, ComplexContext.FamInv D b j₀ m k (hSem D m k c g) G (profQ Δ μ₀ 0 (16 * sizeS D m Cd)) := by
  have hR := repAlgQ_famInvQ (D := D) (b := b) (j₀ := j₀) (m := m) (k := k) (Δ := Δ) (μ₀ := μ₀)
    (π := (id : ℝ × RealChain → ℝ × RealChain)) hΔ
  have hs0 := ownSize_nonneg' env.hΛ1 m
  have hJ : ∀ a e, famInvQ D b j₀ m k Δ μ₀ id (fun l => l.2.famJac D l.1 a e) 0 2 := by
    intro a e
    have h1 := (famInv_ownLeaf env m k (jacSub_entryFun a e)).add
      (ComplexContext.FamInv.time (D := D) (b := b) (j₀ := j₀) (i := m) (p := k)
        (L := TimeLetter.const (if a = e then 1 else 0)) continuous_const)
    refine famInvQ_congr (famInvQ_of_famInv h1 fun mres t _ _ _ => ?_) fun l => ?_
    · simp only [↓reduceIte, profQ_zero_le, Nat.cast_zero, zero_mul, add_zero, TimeLetter.eval]
      split_ifs with h2 h3
      · rw [← ENNReal.ofReal_add hs0 (by positivity)]
        have : ownSize D m + |(1 : ℝ)| ≤ 2 := by rw [abs_one]; linarith
        exact (ENNReal.ofReal_le_ofReal this).trans (by norm_num)
      · exact le_top
      · rw [abs_zero, ENNReal.ofReal_zero, add_zero]
        exact (ENNReal.ofReal_le_ofReal (show ownSize D m ≤ 2 by linarith)).trans (by norm_num)
      · exact le_top
    · simp [GenSort.add, GenSort.ofTime, TimeLetter.eval]
  have hS : ∀ a e, famInvQ D b j₀ m k Δ μ₀ id (fun l => sHat D m k a e l.1 l.2) 0 (sizeS D m Cd) :=
    fun a e => famInvQ_of_famInv (famInv_sHat env hm hκ hk hCd hc hκm hκle a e)
      fun mres t _ _ _ => by
        simp only [↓reduceIte, profQ_zero_le, Nat.cast_zero, zero_mul, add_zero]
        split_ifs
        · exact le_of_eq rfl
        · exact le_top
  have hH := hR.finsetSum Finset.univ (C := fun _ => ∑ e : Fin 2, 2 * sizeS D m Cd * 2)
    fun a _ => hR.finsetSum Finset.univ fun e _ => hR.mul (hR.mul (hJ c a) (hS a e)) (hJ g e)
  obtain ⟨f, G, hf, hF⟩ := hH
  have hfe : f = hSem D m k c g := funext fun t => funext fun A => (hf (t, A)).symm
  subst hfe
  refine ⟨G, hF.mono fun mres t _ _ _ => profQ_mono hΔ le_rfl (le_of_eq ?_) mres t⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- **The family invariant of an inverse Jacobian letter**, of size `2`. -/
theorem famInv_jacInv (env : ChainEnv D b CH Υ j₀) (hm : ownSize D m ≤ 1 / 100) (a e : Fin 2) :
    ∃ G : Ext, ComplexContext.FamInv D b j₀ m k (fun t ch => (ch.famJac D t)⁻¹ a e) G (profQ Δ μ₀ 0 2) := by
  have hs0 := ownSize_nonneg' env.hΛ1 m
  have hB := invB_le_two_mul hs0 hm
  have h1 := (famInv_ownLeaf env m k (invSub_entryFun a e)).add
    (ComplexContext.FamInv.time (D := D) (b := b) (j₀ := j₀) (i := m) (p := k)
      (L := TimeLetter.const (if a = e then 1 else 0)) continuous_const)
  obtain ⟨f, G, hf, hF⟩ := famInvQ_of_famInv (Δ := Δ) (μ₀ := μ₀) (r := 0) (C := 2)
    (π := (id : ℝ × RealChain → ℝ × RealChain)) h1 fun mres t _ _ _ => by
      simp only [↓reduceIte, profQ_zero_le, Nat.cast_zero, zero_mul, add_zero, TimeLetter.eval]
      split_ifs with h2 h3
      · rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        have : ownSize D m * (1 + ownSize D m) / (1 - ownSize D m) ^ 2 + |(1 : ℝ)| ≤ 2 := by
          rw [abs_one]; linarith
        exact (ENNReal.ofReal_le_ofReal this).trans (by norm_num)
      · exact le_top
      · rw [abs_zero, ENNReal.ofReal_zero, add_zero]
        exact (ENNReal.ofReal_le_ofReal (show ownSize D m * (1 + ownSize D m) /
          (1 - ownSize D m) ^ 2 ≤ 2 by linarith)).trans (by norm_num)
      · exact le_top
  have hfe : f = fun t ch => (ch.famJac D t)⁻¹ a e := funext fun t => funext fun ch =>
    (hf (t, ch)).symm.trans (by simp [GenSort.add, GenSort.ofTime, TimeLetter.eval])
  subst hfe
  exact ⟨G, hF⟩

/-- The good pairs: a time of the lift window and a family of the grade-zero setup. -/
abbrev GoodPair (D : OCData) (m : ℕ) (t₀ t₁ : ℝ) (𝒜 : Set RealChain) : Type :=
  {l : ℝ × RealChain // (D.cellScaleSq m)⁻¹ * l.1 ∈ Icc t₀ t₁ ∧ l.2 ∈ 𝒜}

variable {𝒮 : SeedExports} {Dm : ℕ} {𝒜 : Set RealChain} {ρ : ℝ} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N : ℕ}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

/-- **The bridge arrays of the appended children have sized jets**: the point-jets of
`x ↦ hSem(A^{[Ψ⁻¹x]})` on the good pairs. -/
theorem jetRepGQ_bridge (L : ChildLift D b j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc0)
    (env : ChainEnv D b CH Υ j₀) (hm : ownSize D m ≤ 1 / 100)
    (hCd : D.eps m ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap m * D.kap (m - 1)))
    (hc : 0 < D.cellScaleSq m) (hκm : D.kap m = D.κ m) (hκle : D.kap m ≤ D.kap (m - 1))
    (hΔ : 0 < Δ) (hμ : μ₀ ≤ 2) {σ : ℝ≥0}
    (hσ : ENNReal.ofReal (12 / b) / ENNReal.ofReal (D.eps (m - 1) * Δ) ≤ σ) {n : ℕ}
    (hRX : n + Dm + 2 ≤ sX) (hRZ : n + Dm + 2 ≤ sZ) (c g : Fin 2) :
    JetRepGQ (famInvQ D b j₀ m k Δ μ₀ (Subtype.val : GoodPair D m t₀ t₁ 𝒜 → ℝ × RealChain)) σ n
      (fun l y => hSem D m k c g l.1.1 (l.1.2.recenter D (l.1.2.famMapInv D l.1.1 y))) 0
      (compC (invP 2 n) n * (16 * sizeS D m Cd)) := by
  have hR := repAlgQ_famInvQ (D := D) (b := b) (j₀ := j₀) (m := m) (k := k) (Δ := Δ) (μ₀ := μ₀)
    (π := (Subtype.val : GoodPair D m t₀ t₁ 𝒜 → ℝ × RealChain)) hΔ.le
  have hW : ∀ l : GoodPair D m t₀ t₁ 𝒜, l.1.2.WellSlotted := fun l => (L.hS.hA _ l.2.2).1
  obtain ⟨GH, hH⟩ := famInv_hSem (μ₀ := μ₀) env hm L.hκ L.hk hCd hc hκm hκle hΔ.le c g
  have hg := jetRepGQ_covariant_famInvQ (π := (Subtype.val : GoodPair D m t₀ t₁ 𝒜 → ℝ × RealChain))
    env hΔ hμ hσ n hH
  have hInv : ∀ n' a e, JetRepGQ (famInvQ D b j₀ m k Δ μ₀
      (Subtype.val : GoodPair D m t₀ t₁ 𝒜 → ℝ × RealChain)) σ n'
      (fun l w => ((l.1.2.recenter D w).famJac D l.1.1)⁻¹ a e) 0 2 := by
    intro n' a e
    obtain ⟨G, hF⟩ := famInv_jacInv (k := k) (Δ := Δ) (μ₀ := μ₀) env hm a e
    exact jetRepGQ_covariant_famInvQ env hΔ hμ hσ n' hF
  have hΨ := jetRepGQ_dLabel_famMapInv_of hR L.hζ
    (Subtype.val : GoodPair D m t₀ t₁ 𝒜 → ℝ × RealChain) hW hInv
  refine JetRepGQ.comp hR (g := fun (l : GoodPair D m t₀ t₁ 𝒜) w => hSem D m k c g l.1.1
      (l.1.2.recenter D w)) (Ψ := fun (l : GoodPair D m t₀ t₁ 𝒜) y => l.1.2.famMapInv D l.1.1 y)
    (fun l => famMapInv_zero L.hζ l.1.2 l.1.1)
    (fun l => L.contDiff_hSem_recenter l.2.2 l.2.1 hRX hRZ c g)
    (fun l => (contDiff_famMapInv l.1.2 l.1.1).of_le (by exact_mod_cast le_top)) hg
    fun a e => (hΨ n a e).mono hR le_rfl (Nat.zero_le _) le_rfl

/-- The family function of the bridge leaf: the jet `β` at `0` of the entry `(c, g)`. -/
def bridgeLeafFam (D : OCData) (m : ℕ) (k : ℤ) (c g : Fin 2) {r : ℕ} (β : DerivativeWord2 r) :
    GenSort.Sem .fam :=
  fun t A => AVRegularity.orderedDerivative β
    (fun x => hSem D m k c g t (A.recenter D (A.famMapInv D t x))) 0

/-- **The family invariant of a bridge leaf**, of size `σ^r compC(invP 2 n, n) 16 C_Ŝ`. -/
theorem famInv_bridgeLeaf (L : ChildLift D b j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc0)
    (env : ChainEnv D b CH Υ j₀) (hm : ownSize D m ≤ 1 / 100)
    (hCd : D.eps m ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap m * D.kap (m - 1)))
    (hc : 0 < D.cellScaleSq m) (hκm : D.kap m = D.κ m) (hκle : D.kap m ≤ D.kap (m - 1))
    (hΔ : 0 < Δ) (hμ : μ₀ ≤ 2) {σ : ℝ≥0}
    (hσ : ENNReal.ofReal (12 / b) / ENNReal.ofReal (D.eps (m - 1) * Δ) ≤ σ) {n : ℕ}
    (hRX : n + Dm + 2 ≤ sX) (hRZ : n + Dm + 2 ≤ sZ) (c g : Fin 2) {r : ℕ} (hr : r ≤ n)
    (β : DerivativeWord2 r) :
    ∃ (f : GenSort.Sem .fam) (G : Ext),
      (∀ l : GoodPair D m t₀ t₁ 𝒜, bridgeLeafFam D m k c g β l.1.1 l.1.2 = f l.1.1 l.1.2) ∧
      ComplexContext.FamInv D b j₀ m k f G
        (profQ Δ μ₀ r (σ ^ r * (compC (invP 2 n) n * (16 * sizeS D m Cd)))) := by
  have hR := repAlgQ_famInvQ (D := D) (b := b) (j₀ := j₀) (m := m) (k := k) (Δ := Δ) (μ₀ := μ₀)
    (π := (Subtype.val : GoodPair D m t₀ t₁ 𝒜 → ℝ × RealChain)) hΔ.le
  have h := (jetRepGQ_bridge L env hm hCd hc hκm hκle hΔ hμ hσ hRX hRZ c g).orderedDerivative hR
    hr β
  rw [zero_add] at h
  exact h
end

/-! **Ledger, first source: the certificates of the bridge leaves.** Over a slot `pc` of level `i`,
the bridge leaf of the entry `(c, g)` and the jet word `β` is the context function
`leafSem = Σ_k ϖ_{i+1,k}(t) · bridgeLeafFam(t, 𝒜^♮_k)` over the scheduled finer slots `k`
(`leafSem`). It has a holomorphic extension with modes at most
`e^{−6πb|h|} σ^{|β|} compC(invP 2 n, n) 16 C_Ŝ` while `|β|` reserve steps fit in the budget
(`leafSem_cert`): the carrier-calculus evaluation at the appended child (`CtxInv.evalChild`) of the family
invariants of the bridge jets (`famInv_bridgeLeaf`), summed over the finer slots with weights adding
up to at most one (`sum_ocCutoff_mul_le`). -/

section
open AVRegularity.Providers.ComplexContext AVRegularity.Providers.ComplexFlow AVRegularity.Providers.GenSem

variable {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}

/-- A context invariant with an extension that agrees pointwise. -/
theorem ctxInv_congrW {f : GenSort.Sem .ctx} {F F' : Ext} {B : ℝ → ℤ → ℝ → ℝ≥0∞}
    (hF : AVRegularity.Providers.ComplexContext.CtxInv D b j₀ i p f F B) (hG : ∀ dd n t x, F dd n t x = F' dd n t x) :
    AVRegularity.Providers.ComplexContext.CtxInv D b j₀ i p f F' B := by
  have : F = F' := funext fun dd => funext fun n => funext fun t => funext fun x => hG dd n t x
  subst this
  exact hF

/-- **Finite sums of context invariants.** -/
theorem ctxInv_finsetSum (hb : 0 < b) {ι : Type*} (s : Finset ι) {f : ι → GenSort.Sem .ctx}
    {F : ι → Ext} {B : ι → ℝ → ℤ → ℝ → ℝ≥0∞}
    (h : ∀ a ∈ s, AVRegularity.Providers.ComplexContext.CtxInv D b j₀ i p (f a) (F a) (B a)) :
    AVRegularity.Providers.ComplexContext.CtxInv D b j₀ i p (fun t ch ζ => ∑ a ∈ s, f a t ch ζ) (fun dd n t x => ∑ a ∈ s, F a dd n t x)
      (fun mres h t => ∑ a ∈ s, B a mres h t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 := AVRegularity.Providers.ComplexContext.CtxInv.time (D := D) (b := b) (j₀ := j₀) (i := i) (p := p)
      (L := TimeLetter.const 0) continuous_const
    simp only [Finset.sum_empty]
    refine ctxInv_congrW ((h0.congr fun _ _ _ _ _ => rfl).mono fun _ _ _ _ _ _ => ?_)
      fun _ _ _ _ => by simp [TimeLetter.eval]
    simp [TimeLetter.eval]
  | insert a s ha ih =>
    have h1 := AVRegularity.Providers.ComplexContext.CtxInv.add hb (h a (Finset.mem_insert_self a s))
      (ih fun c hc => h c (Finset.mem_insert_of_mem hc))
    simp only [Finset.sum_insert ha]
    exact h1

/-- The bridge leaf of the entry `(c, g)` and the jet word `β` over the finer slots `S`. -/
def leafSem (D : OCData) (i : ℕ) (S : Finset ℤ) (c g : Fin 2) {r : ℕ} (β : DerivativeWord2 r) :
    GenSort.Sem .ctx :=
  fun t ch ζ => ∑ k ∈ S, ocCutoff D.α D.q D.Λ (i + 1) k t *
    bridgeLeafFam D (i + 1) k c g β t (ch.appendChild D k t ζ)

/-- The profile of a bridge leaf: `e^{−6πb|h|} C` while `r` reserve steps fit in the budget. -/
def leafProf (b Δ μ₀ : ℝ) (r : ℕ) (C : ℝ≥0) : ℝ → ℤ → ℝ≥0∞ :=
  fun mres h => if 0 ≤ mres ∧ mres + r * Δ ≤ μ₀ then
    ENNReal.ofReal (Real.exp (-(6 * Real.pi * b * |(h : ℝ)|))) * C else ⊤

variable {CH Υ : ℝ} {𝒮 : SeedExports} {Dm : ℕ} {ρ : ℝ} {sX sZ N : ℕ} {Δ μ₀ Cd : ℝ}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

/-- **The context invariant of a bridge leaf.** -/
theorem leafSem_ctxInv (env : ChainEnv D b CH Υ j₀) (hij : j₀ ≤ i) {pc : ℤ}
    (hm : ownSize D (i + 1) ≤ 1 / 100)
    (hCd : D.eps (i + 1) ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap (i + 1) * D.kap i))
    (hc : 0 < D.cellScaleSq (i + 1)) (hκm : D.kap (i + 1) = D.κ (i + 1))
    (hκle : D.kap (i + 1) ≤ D.kap i) (hΔ : 0 < Δ) (hμ : μ₀ ≤ 2) {σ : ℝ≥0}
    (hσ : ENNReal.ofReal (12 / b) / ENNReal.ofReal (D.eps i * Δ) ≤ σ) {n : ℕ}
    (hRX : n + Dm + 2 ≤ sX) (hRZ : n + Dm + 2 ≤ sZ)
    (𝒜 : ℤ → Set RealChain) (t₀ t₁ : ℤ → ℝ) (S : Finset ℤ)
    (hS : ∀ k ∈ S, Odd k ∧ IsScheduledIn D i k pc)
    (L : ∀ k ∈ S, ChildLift D b j₀ 𝒮 Dm (i + 1) k (𝒜 k) ρ sX sZ (t₀ k) (t₁ k) N Cc0)
    (hgood : ∀ k ∈ S, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i pc, ∀ ch,
      IsAdmissibleChain D b j₀ i pc ch → ∀ ζ, ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0 →
        (D.cellScaleSq (i + 1))⁻¹ * t ∈ Icc (t₀ k) (t₁ k) ∧ ch.appendChild D k t ζ ∈ 𝒜 k)
    (c g : Fin 2) {r : ℕ} (hr : r ≤ n) (β : DerivativeWord2 r) :
    ∃ F : Ext, AVRegularity.Providers.ComplexContext.CtxInv D b j₀ i pc (leafSem D i S c g β) F
      (fun mres h _ => leafProf b Δ μ₀ r
        (σ ^ r * (compC (invP 2 n) n * (16 * sizeS D (i + 1) Cd))) mres h) := by
  classical
  set Cr := σ ^ r * (compC (invP 2 n) n * (16 * sizeS D (i + 1) Cd)) with hCr
  have hstart := startBound_of_carrierStart env.hΛ1 env.hCH env.hΥ env.hcs
  -- the summed invariant, by induction on the finer slots
  have key : ∀ T : Finset ℤ, T ⊆ S → ∃ F : Ext, AVRegularity.Providers.ComplexContext.CtxInv D b j₀ i pc (leafSem D i T c g β) F
      (fun mres h t => ∑ k ∈ T, ENNReal.ofReal (ocCutoff D.α D.q D.Λ (i + 1) k t) *
        (ENNReal.ofReal (Real.exp (-(6 * Real.pi * b * |(h : ℝ)|))) *
          profQ Δ μ₀ r Cr mres 0 t)) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      have h0 := ctxInv_finsetSum (D := D) (b := b) (j₀ := j₀) (i := i) (p := pc) env.hb0
        (∅ : Finset ℤ) (f := fun _ => fun _ _ _ => 0) (F := fun _ => fun _ _ _ _ => 0)
        (B := fun _ => fun _ _ _ => 0) (fun a ha => absurd ha (Finset.notMem_empty a))
      exact ⟨_, (h0.congr fun _ _ _ _ _ => by simp [leafSem]).mono fun _ _ _ _ _ _ => by simp⟩
    | insert a T ha ih =>
      intro hsub
      have haS : a ∈ S := hsub (Finset.mem_insert_self a T)
      obtain ⟨F, hF⟩ := ih fun x hx => hsub (Finset.mem_insert_of_mem hx)
      obtain ⟨f, G, hfa, hFa⟩ := famInv_bridgeLeaf (L a haS) env hm hCd hc hκm hκle hΔ hμ hσ
        hRX hRZ c g hr β
      have hE := AVRegularity.Providers.ComplexContext.CtxInv.evalChild env.hζ env.hΛ1 env.hb0 env.hb1 hstart hij (hS a haS).1
        (hS a haS).2 hFa
      refine ⟨_, ((AVRegularity.Providers.ComplexContext.CtxInv.add env.hb0 hE hF).congr fun t ht ch hch ζ => ?_).mono
        fun mres h t _ _ _ => ?_⟩
      · simp only [GenSort.add, leafSem, Finset.sum_insert ha]
        congr 1
        by_cases h0 : ocCutoff D.α D.q D.Λ (i + 1) a t = 0
        · rw [h0, zero_mul, zero_mul]
        · obtain ⟨hwin, hmem⟩ := hgood a haS t ht ch hch ζ h0
          rw [← hfa ⟨(t, ch.appendChild D a t ζ), hwin, hmem⟩]
      · rw [Finset.sum_insert ha]
        exact le_of_eq (by ring)
  obtain ⟨F, hF⟩ := key S subset_rfl
  refine ⟨F, hF.mono fun mres h t hm0 _ _ => ?_⟩
  unfold leafProf
  split_ifs with hbud
  · have hY : ∀ k ∈ S, ENNReal.ofReal (Real.exp (-(6 * Real.pi * b * |(h : ℝ)|))) *
        profQ Δ μ₀ r Cr mres 0 t ≤ ENNReal.ofReal (Real.exp (-(6 * Real.pi * b * |(h : ℝ)|))) *
          (Cr : ℝ≥0∞) := fun k _ => by
      simp only [profQ_zero_le, hbud.2, ↓reduceIte, le_refl]
    exact sum_ocCutoff_mul_le (Construction.Stream.ocTau_pos env.hΛ1) S
      (fun k hk => (hS k hk).1) t _ hY
  · exact le_top

/-- **The certificate of a bridge leaf**: a holomorphic extension with modes below `leafProf`. -/
theorem leafSem_cert (env : ChainEnv D b CH Υ j₀) (hij : j₀ ≤ i) {pc : ℤ}
    (hm : ownSize D (i + 1) ≤ 1 / 100)
    (hCd : D.eps (i + 1) ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap (i + 1) * D.kap i))
    (hc : 0 < D.cellScaleSq (i + 1)) (hκm : D.kap (i + 1) = D.κ (i + 1))
    (hκle : D.kap (i + 1) ≤ D.kap i) (hΔ : 0 < Δ) (hμ : μ₀ ≤ 2) {σ : ℝ≥0}
    (hσ : ENNReal.ofReal (12 / b) / ENNReal.ofReal (D.eps i * Δ) ≤ σ) {n : ℕ}
    (hRX : n + Dm + 2 ≤ sX) (hRZ : n + Dm + 2 ≤ sZ)
    (𝒜 : ℤ → Set RealChain) (t₀ t₁ : ℤ → ℝ) (S : Finset ℤ)
    (hS : ∀ k ∈ S, Odd k ∧ IsScheduledIn D i k pc)
    (L : ∀ k ∈ S, ChildLift D b j₀ 𝒮 Dm (i + 1) k (𝒜 k) ρ sX sZ (t₀ k) (t₁ k) N Cc0)
    (hgood : ∀ k ∈ S, ∀ t ∈ ocPulseWindow D.α D.q D.Λ i pc, ∀ ch,
      IsAdmissibleChain D b j₀ i pc ch → ∀ ζ, ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0 →
        (D.cellScaleSq (i + 1))⁻¹ * t ∈ Icc (t₀ k) (t₁ k) ∧ ch.appendChild D k t ζ ∈ 𝒜 k)
    (c g : Fin 2) {r : ℕ} (hr : r ≤ n) (β : DerivativeWord2 r) :
    ∃ F : Ext, IsHolExtension D b j₀ i pc (leafSem D i S c g β) F ∧ ∀ (mres : ℝ) (h : ℤ),
      ctxModeSup D b j₀ i pc F mres h ≤
        leafProf b Δ μ₀ r (σ ^ r * (compC (invP 2 n) n * (16 * sizeS D (i + 1) Cd))) mres h := by
  obtain ⟨F, hF⟩ := leafSem_ctxInv env hij hm hCd hc hκm hκle hΔ hμ hσ hRX hRZ 𝒜 t₀ t₁ S hS L
    hgood c g hr β
  refine ⟨trimExt D b F, hF.isHolExtension env.hΛ1 env.hb0, fun mres h => ?_⟩
  by_cases hbud : 0 ≤ mres ∧ mres + r * Δ ≤ μ₀
  · have hm2 : mres ≤ 2 := by
      have : 0 ≤ (r : ℝ) * Δ := mul_nonneg (Nat.cast_nonneg r) hΔ.le
      linarith [hbud.2]
    unfold ctxModeSup
    refine iSup₂_le fun dd n' => iSup_le fun hex => iSup₂_le fun t ht => ?_
    refine iSup₂_le fun x hx => iSup_le fun hre => ?_
    refine le_trans ?_ (hF.ctxModeSupAt_trim_le env.hb0 hbud.1 hm2 h ht)
    unfold ctxModeSupAt
    exact le_iSup₂_of_le dd n' (le_iSup_of_le hex (le_iSup₂_of_le x hx (le_iSup_of_le hre le_rfl)))
  · unfold leafProf
    simp only [hbud, ↓reduceIte, le_top]
end

/-! **Ledger, first source: sized context functions.** The context instance of the sized jet
calculus. A context function of the index `l : CtxIdx P` is *sized* (`ctxAlgQ X`) with cost `r`
and size `C` when it is represented (`CtxRep`) by a scheduled expression without uncertified
solved node whose structural norm (`genNorm`, outer rate `X.a`, with the leaf map `X.leaf`) is at
most `C` whenever `r` reserve steps and `r` fast weights fit in the budgets. Sums add and
products multiply the sizes (`repAlgQ_ctxAlgQ`).

The certified leaves of the first source are *marked*: `markE n e = 1 · e + 0 · ϖ_{0,n}`
(a context-sorted partition letter, which the calculus never builds), so that the leaf map fires
only on expressions of the marker shape (`isMarkShape`), and every node built by the calculus is
not a leaf as long as it is not a partition letter nor a product with one on the right
(`NoMark`, an invariant of the construction). `markLeaf` is the leaf map of a family of marked
expressions with an injective code. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

/-! ### Markers -/

/-- The leaf marker `1 · e + 0 · ϖ_{0,n}`. -/
def markE (n : ℤ) {i : ℕ} {p : ℤ} (e : Gen .ctx i p) : Gen .ctx i p :=
  Gen.add (Gen.mul (Gen.time (.const 1)) e)
    (Gen.mul (Gen.time (.const 0)) (Gen.time (.partition 0 n)))

/-- The marker shape. -/
def isMarkShape : {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → Prop
  | _, _, _, .add _ (.mul (.time (.const _)) (.time (.partition _ _))) => True
  | _, _, _, _ => False

/-- The code of a marked expression. -/
def markCode : {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → ℤ
  | _, _, _, .add _ (.mul _ (.time (.partition _ n))) => n
  | _, _, _, _ => 0

theorem isMarkShape_markE (n : ℤ) {i : ℕ} {p : ℤ} (e : Gen .ctx i p) : isMarkShape (markE n e) :=
  trivial

theorem markCode_markE (n : ℤ) {i : ℕ} {p : ℤ} (e : Gen .ctx i p) : markCode (markE n e) = n := rfl

/-- Neither a partition letter nor a product with a partition letter on the right. -/
def NoMark : {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → Prop
  | _, _, _, .time (.partition _ _) => False
  | _, _, _, .mul _ (.time (.partition _ _)) => False
  | _, _, _, _ => True

theorem noMark_add {s : GenSort} {i : ℕ} {p : ℤ} (x y : Gen s i p) : NoMark (Gen.add x y) :=
  trivial

theorem noMark_mul {s : GenSort} {i : ℕ} {p : ℤ} (x : Gen s i p) {y : Gen s i p}
    (hy : NoMark y) : NoMark (Gen.mul x y) := by
  cases y with
  | time L => cases L <;> first | exact absurd hy id | trivial
  | _ => trivial

theorem not_isMarkShape_time {s : GenSort} {i : ℕ} {p : ℤ} (L : TimeLetter) :
    ¬ isMarkShape (Gen.time (s := s) (i := i) (p := p) L) := id

theorem not_isMarkShape_mul {s : GenSort} {i : ℕ} {p : ℤ} (x y : Gen s i p) :
    ¬ isMarkShape (Gen.mul x y) := id

theorem not_isMarkShape_add {s : GenSort} {i : ℕ} {p : ℤ} (x : Gen s i p) {y : Gen s i p}
    (hy : NoMark y) : ¬ isMarkShape (Gen.add x y) := by
  cases y with
  | mul u v =>
    cases u with
    | time L =>
      cases L with
      | const c =>
        cases v with
        | time L' => cases L' <;> first | exact absurd hy id | exact id
        | _ => exact id
      | _ => exact id
    | _ => exact id
  | _ => exact id

/-! ### The leaf map of marked expressions -/

section MarkLeaf

variable {ι : Type*} (i₀ : ℕ) (slot : ι → ℤ) (code : ι → ℤ)
  (E : (x : ι) → Gen .ctx i₀ (slot x)) (B : ι → ℝ → ℤ → ℝ≥0∞)

open scoped Classical in
/-- **The leaf map of a family of marked expressions.** -/
def markLeaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞) :=
  fun {s i p} e =>
    if h : ∃ x : ι, (⟨.ctx, i₀, slot x, markE (code x) (E x)⟩ :
        Σ (s : GenSort) (i : ℕ) (p : ℤ), Gen s i p) = ⟨s, i, p, e⟩ then
      some (B (Classical.choose h))
    else none

variable {i₀ slot code E B}

/-- The leaf map fires only on the marker shape. -/
theorem markLeaf_eq_none {s : GenSort} {i : ℕ} {p : ℤ} {e : Gen s i p} (he : ¬ isMarkShape e) :
    markLeaf i₀ slot code E B e = none := by
  classical
  unfold markLeaf
  split_ifs with h
  · obtain ⟨x, hx⟩ := h
    have := congrArg (fun σ : Σ (s : GenSort) (i : ℕ) (p : ℤ), Gen s i p => isMarkShape σ.2.2.2)
      hx
    simp only at this
    exact absurd (this ▸ isMarkShape_markE (code x) (E x)) he
  · rfl

/-- **A marked expression carries its own profile.** -/
theorem markLeaf_markE (hcode : Function.Injective code) (x : ι) :
    markLeaf i₀ slot code E B (markE (code x) (E x)) = some (B x) := by
  classical
  have h : ∃ y : ι, (⟨.ctx, i₀, slot y, markE (code y) (E y)⟩ :
      Σ (s : GenSort) (i : ℕ) (p : ℤ), Gen s i p) = ⟨.ctx, i₀, slot x, markE (code x) (E x)⟩ :=
    ⟨x, rfl⟩
  unfold markLeaf
  rw [dite_eq_left_of_eq_true (eq_true h)]
  congr 2
  apply hcode
  have hc := congrArg (fun σ : Σ (s : GenSort) (i : ℕ) (p : ℤ), Gen s i p => markCode σ.2.2.2)
    (Classical.choose_spec h)
  simpa only [markCode_markE] using hc

/-- The leaf map fires only on context expressions. -/
theorem markLeaf_eq_none_of_ne {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p) (hs : s ≠ .ctx) :
    markLeaf i₀ slot code E B e = none := by
  classical
  unfold markLeaf
  split_ifs with h
  · obtain ⟨x, hx⟩ := h
    exact absurd (congrArg Sigma.fst hx).symm hs
  · rfl

/-- The expressions on which the leaf map fires are the marked ones, with their profiles. -/
theorem markLeaf_eq_some {s : GenSort} {i : ℕ} {p : ℤ} {e : Gen s i p}
    {Bx : ℝ → ℤ → ℝ≥0∞} (he : markLeaf i₀ slot code E B e = some Bx) :
    ∃ x : ι, (⟨.ctx, i₀, slot x, markE (code x) (E x)⟩ :
        Σ (s : GenSort) (i : ℕ) (p : ℤ), Gen s i p) = ⟨s, i, p, e⟩ ∧ Bx = B x := by
  classical
  unfold markLeaf at he
  split_ifs at he with h
  · exact ⟨Classical.choose h, Classical.choose_spec h, (Option.some.inj he).symm⟩

end MarkLeaf

/-! ### Sized context functions -/

/-- The parameters of the sized context calculus: carrier constants, reserve step, outer and
inner rates, reserve and fast-weight budgets, and the leaf map. -/
structure CCtx where
  /-- The carrier constants. -/
  κ : MajConsts
  /-- The reserve step. -/
  Δ : ℝ
  /-- The outer rate. -/
  a : ℝ
  /-- The inner rate. -/
  a₀ : ℝ
  /-- The reserve budget. -/
  μ₀ : ℝ
  /-- The fast-weight budget. -/
  L₀ : ℕ
  /-- The certified leaves. -/
  leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)

/-- The standing hypotheses of the sized context calculus. -/
structure CCtx.Ok (X : CCtx) : Prop where
  /-- The reserve step is nonnegative. -/
  hΔ : 0 ≤ X.Δ
  /-- The budget lies inside the outer reserve. -/
  hμ : X.μ₀ ≤ 2
  /-- The leaves have the marker shape. -/
  hshape : ∀ {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p), ¬ isMarkShape e → X.leaf e = none
  /-- The leaves are context expressions. -/
  hctx : ∀ (s : GenSort) (i : ℕ) (p : ℤ) (e : Gen s i p), s ≠ .ctx → X.leaf e = none

variable (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (i : ℕ) (pc : ℤ)
  (P : ℝ → RealChain → Vec 2 → Prop) (X : CCtx)

/-- **Sized context functions.** -/
def ctxAlgQ : (CtxIdx P → ℝ) → ℕ → ℝ≥0 → Prop :=
  fun F r C => ∃ (φ : ℝ → RealChain → Vec 2 → ℝ) (e : Gen .ctx i pc),
    (∀ l : CtxIdx P, F l = φ l.1.1 l.1.2.1 l.1.2.2) ∧ CtxRep D bw j₀ 𝒮 P φ e ∧
    Gen.SolvedFree X.leaf e ∧ NoMark e ∧
    ∀ t ∈ ocPulseWindow D.α D.q D.Λ i pc, ∀ (mres : ℝ) (L : ℕ), 0 ≤ mres →
      mres + r * X.Δ ≤ X.μ₀ → L + r ≤ X.L₀ → genNorm D X.κ X.Δ X.a₀ X.leaf e X.a mres L t ≤ C

variable {D bw j₀ 𝒮 i pc P X}

theorem repAlgQ_ctxAlgQ (hX : X.Ok) : RepAlgQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) where
  mono {F r r' C C'} h hr hC := by
    obtain ⟨φ, e, hF, hR, hs, hn, hb⟩ := h
    refine ⟨φ, e, hF, hR, hs, hn, fun t ht mres L hm0 hm hL => ?_⟩
    have hrr : (r : ℝ) * X.Δ ≤ (r' : ℝ) * X.Δ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hr) hX.hΔ
    exact (hb t ht mres L hm0 (by linarith) (by omega)).trans (by exact_mod_cast hC)
  const c := ⟨fun _ _ _ => c, Gen.time (.const c), fun _ => rfl, CtxRep.const c, trivial, trivial,
    fun t _ mres L _ _ _ => by
      exact (genNorm_const_le X.κ X.Δ X.a₀ X.leaf (D := D) c
        (hX.hshape _ (not_isMarkShape_time _)) X.a mres L t).trans (le_of_eq rfl)⟩
  add := fun ⟨φ₁, e₁, hF₁, hR₁, hs₁, hn₁, hb₁⟩ ⟨φ₂, e₂, hF₂, hR₂, hs₂, hn₂, hb₂⟩ =>
    ⟨fun t ch z => φ₁ t ch z + φ₂ t ch z, Gen.add e₁ e₂, fun l => by simp [hF₁ l, hF₂ l],
      hR₁.add hR₂, Or.inr ⟨hs₁, hs₂⟩, noMark_add _ _, fun t ht mres L hm0 hm hL => by
        rw [genNorm_add_eq D X.κ X.Δ X.a₀ X.leaf (hX.hshape _ (not_isMarkShape_add _ hn₂))]
        rw [ENNReal.coe_add]
        exact add_le_add (hb₁ t ht mres L hm0 hm hL) (hb₂ t ht mres L hm0 hm hL)⟩
  mul := fun ⟨φ₁, e₁, hF₁, hR₁, hs₁, hn₁, hb₁⟩ ⟨φ₂, e₂, hF₂, hR₂, hs₂, hn₂, hb₂⟩ =>
    ⟨fun t ch z => φ₁ t ch z * φ₂ t ch z, Gen.mul e₁ e₂, fun l => by simp [hF₁ l, hF₂ l],
      hR₁.mul hR₂, Or.inr ⟨hs₁, hs₂⟩, noMark_mul _ hn₂, fun t ht mres L hm0 hm hL => by
        rw [genNorm_mul_eq D X.κ X.Δ X.a₀ X.leaf (hX.hshape _ (not_isMarkShape_mul _ _))]
        rw [ENNReal.coe_mul]
        exact mul_le_mul' (hb₁ t ht mres L hm0 hm hL) (hb₂ t ht mres L hm0 hm hL)⟩

/-- **A time letter** is a sized context function with the size of its values. -/
theorem ctxAlgQ_time (hX : X.Ok) (Lt : TimeLetter)
    (hs : Gen.IsScheduled D (Gen.time (s := .ctx) (i := i) (p := pc) Lt))
    (hLt : NoMark (Gen.time (s := .ctx) (i := i) (p := pc) Lt)) {C : ℝ≥0}
    (hC : ∀ t ∈ ocPulseWindow D.α D.q D.Λ i pc, |Lt.eval D t| ≤ C) :
    ctxAlgQ D bw j₀ 𝒮 i pc P X (fun l => Lt.eval D l.1.1) 0 C := by
  refine ⟨fun t _ _ => Lt.eval D t, Gen.time Lt, fun _ => rfl,
    ⟨hs, .time _, GenSort.ofTime .ctx (Lt.eval D), .time _, fun _ _ _ _ => rfl⟩, trivial,
    hLt, fun t ht mres L _ _ _ => ?_⟩
  simp only [genNorm, hX.hshape _ (not_isMarkShape_time Lt), Option.elim]
  exact (ENNReal.ofReal_le_ofReal (hC t ht)).trans (le_of_eq ENNReal.ofReal_coe_nnreal)
end

/-! **Ledger, first source: the atoms of the sized context calculus.**
* `jetRepGQ_covariant_ctxQ`: a covariant context function (its value at the label `w` is the
  denotation at the recentered context) has sized jets; a label derivative is the old-label
  derivative `dOld`, of cost one reserve step and one fast weight and the factor
  `σ ≥ C_old/(ε_iΔ) + 2π/ε_i` (`genNorm_dOld_le`);
* `ctxAlgQ_mark`: a marked certified leaf has the size of its weighted profile;
* `jetRepGQ_sumEvalChildQ` (in `Diag.SizeQ`): the cutoff-weighted sum of the evaluations at the
  appended children of sized family jets (`famAlgQ` over the graded context `X.toG`), of size
  `W · C` with `W ≥ wsum a L κ.child`. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

/-- The graded family context of a context calculus. -/
def CCtx.toG (X : CCtx) (S Kg Kd : ℝ≥0) : GCtx :=
  ⟨X.κ, X.Δ, X.a₀, X.leaf, X.μ₀, X.L₀, Set.univ, S, Kg, Kd⟩

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {pc : ℤ}
  {P : ℝ → RealChain → Vec 2 → Prop} {X : CCtx}

/-- **Covariant context functions have sized jets.** -/
theorem jetRepGQ_covariant_ctxQ (hX : X.Ok) (hζ : IsFastProfile D.ζ) {σ : ℝ≥0}
    (hσ : X.κ.Cold / ENNReal.ofReal (D.eps i * X.Δ) + ENNReal.ofReal (2 * Real.pi / D.eps i) ≤ σ) :
    ∀ (n : ℕ) {g : CtxIdx P → Vec 2 → ℝ} {a : Gen .ctx i pc} {fa : GenSort.Sem .ctx} {r : ℕ}
      {C : ℝ≥0}, Gen.IsScheduled D a → Gen.FromSeed 𝒮 a → Gen.Denotes D bw j₀ a fa →
      Gen.SolvedFree X.leaf a → NoMark a →
      (∀ t ∈ ocPulseWindow D.α D.q D.Λ i pc, ∀ (mres : ℝ) (L : ℕ), 0 ≤ mres →
        mres + r * X.Δ ≤ X.μ₀ → L + r ≤ X.L₀ → genNorm D X.κ X.Δ X.a₀ X.leaf a X.a mres L t ≤ C) →
      (∀ l w, g l w = fa l.1.1 (l.1.2.1.recenter D w) (l.1.2.2 + (D.eps i)⁻¹ • w)) →
      JetRepGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ n g r C := by
  intro n
  induction n with
  | zero =>
    intro g a fa r C hs hf hd hsf hn hb hg
    refine ⟨fun t ch z => fa t ch z, a, fun l => ?_, ⟨hs, hf, fa, hd, fun _ _ _ _ => rfl⟩, hsf,
      hn, hb⟩
    show g l 0 = fa _ _ _
    rw [hg l 0, recenter_zero D hζ, smul_zero, add_zero]
  | succ n ih =>
    intro g a fa r C hs hf hd hsf hn hb hg
    refine ⟨⟨fun t ch z => fa t ch z, a, fun l => ?_, ⟨hs, hf, fa, hd, fun _ _ _ _ => rfl⟩, hsf,
      hn, hb⟩, fun j => ?_⟩
    · show g l 0 = fa _ _ _
      rw [hg l 0, recenter_zero D hζ, smul_zero, add_zero]
    refine ih (a := Gen.dOld j a) (.dOld j hs) (.dOld j hf) (.dOld j hd) (Or.inr hsf) trivial
      (fun t ht mres L hm0 hm hL => ?_) fun l w => ?_
    · refine (genNorm_dOld_le D X.κ X.Δ X.a₀ X.leaf j a (hX.hshape _ id) X.a mres L t).trans ?_
      have hr0 : 0 ≤ (r : ℝ) * X.Δ := mul_nonneg (Nat.cast_nonneg r) hX.hΔ
      have h1 : mres + X.Δ + r * X.Δ ≤ X.μ₀ := by push_cast at hm; linarith
      have h2 : mres + X.Δ ≤ 2 := by linarith [hX.hμ]
      unfold tStep
      simp only [h2, ↓reduceIte]
      have hA := hb t ht (mres + X.Δ) L (by linarith [hX.hΔ]) h1 (by omega)
      have hB := hb t ht mres (L + 1) hm0 (by push_cast at hm; linarith [hX.hΔ]) (by omega)
      calc X.κ.Cold / ENNReal.ofReal (D.eps i * X.Δ) *
            genNorm D X.κ X.Δ X.a₀ X.leaf a X.a (mres + X.Δ) L t +
          ENNReal.ofReal (2 * Real.pi / D.eps i) *
            genNorm D X.κ X.Δ X.a₀ X.leaf a X.a mres (L + 1) t
          ≤ X.κ.Cold / ENNReal.ofReal (D.eps i * X.Δ) * C +
              ENNReal.ofReal (2 * Real.pi / D.eps i) * C := by gcongr
        _ = (X.κ.Cold / ENNReal.ofReal (D.eps i * X.Δ) +
              ENNReal.ofReal (2 * Real.pi / D.eps i)) * C := by ring
        _ ≤ σ * C := mul_le_mul' hσ le_rfl
        _ = ((σ * C : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl
    · simp only [dLabelG]
      have hev : g l = fun w' => fa l.1.1 (l.1.2.1.recenter D w') (l.1.2.2 + (D.eps i)⁻¹ • w') :=
        funext fun w' => hg l w'
      rw [hev]
      exact (dOld_along hζ i fa l.1.1 l.1.2.1 l.1.2.2 w j).symm

/-- **A marked certified leaf** is a sized context function with the size of its weighted
profile. -/
theorem ctxAlgQ_mark (n : ℤ) {e : Gen .ctx i pc} {φ : ℝ → RealChain → Vec 2 → ℝ}
    (he : CtxRep D bw j₀ 𝒮 P φ e) {B : ℝ → ℤ → ℝ≥0∞}
    (hleaf : X.leaf (markE n e) = some B) {r : ℕ} {C : ℝ≥0}
    (hB : ∀ (mres : ℝ) (L : ℕ), 0 ≤ mres → mres + r * X.Δ ≤ X.μ₀ → L + r ≤ X.L₀ →
      wsum X.a L (B mres) ≤ C) :
    ctxAlgQ D bw j₀ 𝒮 i pc P X (fun l => φ l.1.1 l.1.2.1 l.1.2.2) r C := by
  have hpart : CtxRep D bw j₀ 𝒮 P (fun t _ _ => TimeLetter.eval D (.partition 0 n) t)
      (Gen.time (s := .ctx) (i := i) (p := pc) (.partition 0 n)) :=
    ⟨.timePartition 0 n, .time _, GenSort.ofTime .ctx _, .time _, fun _ _ _ _ => rfl⟩
  refine ⟨φ, markE n e, fun _ => rfl,
    (((CtxRep.const 1).mul he).add ((CtxRep.const 0).mul hpart)).congr fun t ch z _ => by ring,
    Or.inl (by simp only [markE] at hleaf; simp [hleaf]), noMark_add _ _,
    fun t _ mres L hm0 hm hL => ?_⟩
  unfold markE
  simp only [genNorm, show X.leaf (Gen.add (Gen.mul (Gen.time (.const 1)) e)
    (Gen.mul (Gen.time (.const 0)) (Gen.time (.partition 0 n)))) = some B from hleaf,
    Option.elim]
  exact hB mres L hm0 hm hL

/-- Sized family functions restrict to smaller windows. -/
theorem famAlgQ_restrict {m : ℕ} {k : ℤ} {W W' : Set (ℝ × RealChain)} (hW : W' ⊆ W)
    {Xg : GCtx} {F : W → ℝ} {r : ℕ} {C : ℝ≥0} (hF : famAlgQ D bw j₀ 𝒮 m k W Xg F r C) :
    famAlgQ D bw j₀ 𝒮 m k W' Xg (fun q => F ⟨q.1, hW q.2⟩) r C := by
  obtain ⟨c, hs, hf, ⟨fc, hd, hv⟩, hsf, hn⟩ := hF
  exact ⟨c, hs, hf, ⟨fc, hd, fun q => hv ⟨q.1, hW q.2⟩⟩, hsf, hn⟩
end

end AVRegularity.Providers.CascadeInvariants
end

section
open Homogenization AVRegularity AVRegularity.Sobolev Filter Topology
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, first source: the sized strain and commutator arrays.** The sized twins of the
context-level representations of the module `GenSem.First.RepMain`, over the sized context
calculus `ctxAlgQ X`, with the geometric letters bounded by
`W_g ≥ geoW X.κ X.a L` (`L ≤ X.L₀`):
* the chart leaves of the context family: the first derivatives of the centered map
  (`jetRepGQ_ctx_dLabel_famMapQ`, size `W_g`), of its inverse
  (`jetRepGQ_ctx_dLabel_famMapInvQ`, size `invP W_g n`) and the inverse Jacobian
  (`jetRepGQ_ctx_jacInvQ`, size `W_g`);
* the covariance matrix as a time letter (`ctxAlgQ_covMat`);
* the strain field `x ↦ S(x)` (`jetRepGQ_strainAtQ`): the covariant child strain letter
  `a_i · 𝗌` composed with the inverse chart, of size `compC (invP W_g n) n · a_i W_g`;
* the commutator arrays `𝒥_H = −(S H + H Sᵀ)∇` (`arrJetGQ_jhArr`), of the constant
  `4 · 2^n C_S c_H w` for `|H| ≤ c_H w²`. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {pc : ℤ}
  {P : ℝ → RealChain → Vec 2 → Prop} {X : CCtx} {σ : ℝ≥0} {Wg : ℝ≥0}

/-- A geometric letter has the structural norm `W_g` on the fast weights up to `L₀`. -/
theorem genNorm_geo_leW (hX : X.Ok) (hWg : ∀ L, L ≤ X.L₀ → geoW X.κ X.a L ≤ Wg)
    (fr : GenFrame) (Lt : GeoLetter) (mres : ℝ) {L : ℕ} (hL : L ≤ X.L₀) (t : ℝ) :
    genNorm D X.κ X.Δ X.a₀ X.leaf (Gen.geo (i := i) (p := pc) fr Lt) X.a mres L t ≤ Wg := by
  rw [genNorm_geo_eq _ _ _ _ _ fr Lt (hX.hshape _ id)]
  exact (le_iSup₂ (f := fun fr Lt => wsum X.a L (X.κ.geo fr Lt)) fr Lt).trans (hWg L hL)

variable (hX : X.Ok) (hζ : IsFastProfile D.ζ)
  (hσ : X.κ.Cold / ENNReal.ofReal (D.eps i * X.Δ) + ENNReal.ofReal (2 * Real.pi / D.eps i) ≤ σ)
  (hWg : ∀ L, L ≤ X.L₀ → geoW X.κ X.a L ≤ Wg)
include hX hζ hσ hWg

/-- **A covariant own-frame letter** has sized context jets of size `W_g`. -/
theorem jetRepGQ_geoOwnQ (Lt : GeoLetter) (n : ℕ) :
    JetRepGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ n
      (fun l w => Lt.evalAt D (l.1.2.1.recenter D w) l.1.1) 0 Wg :=
  jetRepGQ_covariant_ctxQ hX hζ hσ n (a := Gen.geo (i := i) (p := pc) .own Lt) (.geoOwn _)
    (.geo _ _) (.geo _ _) trivial trivial
    (fun t _ mres L _ _ hL => (genNorm_geo_leW hX hWg .own Lt mres (by omega) t))
    fun _ _ => rfl

/-- **The first derivatives of the centered map of the contexts** have sized jets. -/
theorem jetRepGQ_ctx_dLabel_famMapQ (hW : ∀ l : CtxIdx P, l.1.2.1.WellSlotted) (n : ℕ)
    (b j : Fin 2) :
    JetRepGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ n
      (dLabelG j (fun l y => l.1.2.1.famMap D l.1.1 y b)) 0 Wg :=
  (jetRepGQ_geoOwnQ hX hζ hσ hWg (.jac b j) n).congr_germ fun l =>
    Filter.Eventually.of_forall fun w => by
      simp only [dLabelG]
      rw [dLabel_famMap hζ l.1.2.1 (hW l) l.1.1 b j w]
      rfl

/-- **The inverse Jacobian of the centered map of the contexts** has sized jets. -/
theorem jetRepGQ_ctx_jacInvQ (hW : ∀ l : CtxIdx P, l.1.2.1.WellSlotted) (n : ℕ) (c k : Fin 2) :
    JetRepGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ n
      (fun l x => ((jacMatrix (l.1.2.1.famMap D l.1.1) x)⁻¹) c k) 0 Wg :=
  (jetRepGQ_geoOwnQ hX hζ hσ hWg (.jacInv c k) n).congr_germ fun l =>
    Filter.Eventually.of_forall fun x => by
      show GeoLetter.evalAt D (l.1.2.1.recenter D x) l.1.1 (GeoLetter.jacInv c k) =
        (jacMatrix (l.1.2.1.famMap D l.1.1) x)⁻¹ c k
      rw [jacMatrix_famMap hζ l.1.2.1 (hW l) l.1.1 x]
      rfl

/-- **The first derivatives of the inverse centered map of the contexts** have sized jets. -/
theorem jetRepGQ_ctx_dLabel_famMapInvQ (hW : ∀ l : CtxIdx P, l.1.2.1.WellSlotted) (n : ℕ)
    (b j : Fin 2) :
    JetRepGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ n
      (dLabelG j (fun l x => l.1.2.1.famMapInv D l.1.1 x b)) 0 (invP Wg n) :=
  jetRepGQ_dLabel_famMapInv_of (repAlgQ_ctxAlgQ hX) hζ (fun l : CtxIdx P => (l.1.1, l.1.2.1)) hW
    (fun n' b' j' => jetRepGQ_geoOwnQ hX hζ hσ hWg (.jacInv b' j') n') n b j

omit hζ hσ hWg in
/-- **The covariance matrix** is a sized context function with the size of its values. -/
theorem ctxAlgQ_covMat (hκ : D.kap (i + 1) = D.κ (i + 1)) (hκ' : D.kap i = D.κ i) {C : ℝ≥0}
    (hC : ∀ t ∈ ocPulseWindow D.α D.q D.Λ i pc, ∀ a b, |covMat D (i + 1) 0 t a b| ≤ C)
    (a b : Fin 2) :
    ctxAlgQ D bw j₀ 𝒮 i pc P X (fun l => covMat D (i + 1) 0 l.1.1 a b) 0 C := by
  have e : ∀ t, (TimeLetter.covPrimitive (i + 1) 0 a b).eval D t = covMat D (i + 1) 0 t a b :=
    fun t => by simp only [covMat, TimeLetter.eval, hκ, Nat.add_sub_cancel, hκ']
  have h := ctxAlgQ_time (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := i) (pc := pc) (P := P) hX
    (.covPrimitive (i + 1) 0 a b) (.timeCov _ _ _) (by trivial) (C := C)
    fun t ht => by rw [e]; exact hC t ht a b
  simpa only [e] using h

/-- **Sized context jets of the strain field** `x ↦ S_c(x)`. -/
theorem jetRepGQ_strainAtQ (hΛ : 1 ≤ D.Λ)
    (hP : ∀ l : CtxIdx P, l.1.2.1.WellSlotted ∧ l.1.2.1.ctxLevel = i ∧ l.1.2.1.slot = pc)
    {p' : ℤ} (hp' : IsScheduledIn D i p' pc) (n : ℕ)
    (hreg : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ n (fun y =>
      contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c))
    (a c : Fin 2) :
    JetRepGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ n
      (fun l x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a c) 0
      (compC (invP Wg n) n * (Real.toNNReal (ocA D.α D.q D.Λ i) * Wg)) := by
  have hR := repAlgQ_ctxAlgQ (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := i) (pc := pc)
    (P := P) hX
  have key : ∀ (t : ℝ) (ch' : RealChain) (ζ' : Vec 2), ch'.WellSlotted → ch'.ctxLevel = i →
      ch'.slot = pc → contextStrain D i pc t ch' ζ' = (ch'.appendChild D p' t ζ').famStrain D t := by
    intro t ch' ζ' hw h1 h2
    rw [← h1, ← h2]
    exact contextStrain_eq_childStrain D hζ hΛ ch' hw p' t ζ'
  have hA0 : 0 < ocA D.α D.q D.Λ i :=
    Real.rpow_pos_of_pos (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ) _
  have hA : ocA D.α D.q D.Λ i ≠ 0 := hA0.ne'
  have hG : JetRepGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ n (fun l y =>
      contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c) 0
      (Real.toNNReal (ocA D.α D.q D.Λ i) * Wg) := by
    refine jetRepGQ_covariant_ctxQ hX hζ hσ n (a := Gen.mul (Gen.time (.const (ocA D.α D.q D.Λ i)))
        (Gen.geo (i := i) (p := pc) (.child p') (.strain a c)))
      (.mul (.timeConst _) (.geoChild p' _ hp')) (.mul (.time _) (.geo _ _))
      (.mul (.time _) (.geo _ _)) (Or.inr ⟨trivial, trivial⟩) (noMark_mul _ (by trivial))
      (fun t _ mres L _ _ hL => ?_) fun l w => ?_
    · rw [genNorm_mul_eq _ _ _ _ _ (hX.hshape _ (not_isMarkShape_mul _ _)),
        genNorm_const_eq _ _ _ _ _ _ (hX.hshape _ (not_isMarkShape_time _)), ENNReal.coe_mul,
        abs_of_pos hA0]
      exact mul_le_mul' (le_of_eq rfl) (genNorm_geo_leW hX hWg _ _ mres (by omega) t)
    · obtain ⟨hws, hlev, hslot⟩ := hP l
      have hw := recenter_wellSlotted D _ hws w
      have hlev' : (l.1.2.1.recenter D w).ctxLevel = i := by rw [recenter_ctxLevel]; exact hlev
      rw [key _ _ _ hw.1 hlev' (by rw [hw.2]; exact hslot)]
      have hll : ((l.1.2.1.recenter D w).appendChild D p' l.1.1
          (l.1.2.2 + (D.eps i)⁻¹ • w)).lastLevel = i := by
        rw [← hlev']
        simp only [RealChain.appendChild, RealChain.lastLevel, RealChain.ctxLevel,
          List.length_append, List.length_singleton]
        omega
      simp only [GenSort.mul, GenSort.ofTime, TimeLetter.eval, GeoLetter.eval,
        GeoLetter.isStrain, true_or, ite_true, GeoLetter.evalAt, hll]
      field_simp
  have hW : ∀ l : CtxIdx P, l.1.2.1.WellSlotted := fun l => (hP l).1
  have hcomp := JetRepGQ.comp hR (n := n)
    (g := fun l y => contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c)
    (Ψ := fun l x => l.1.2.1.famMapInv D l.1.1 x) (fun l => famMapInv_zero hζ _ _)
    (fun l => hreg l a c) (fun l => (contDiff_famMapInv _ _).of_le (by exact_mod_cast le_top)) hG
    (fun b j => (jetRepGQ_ctx_dLabel_famMapInvQ hX hζ hσ hWg hW n b j).mono hR le_rfl
      (Nat.zero_le _) le_rfl)
  refine hcomp.congr_germ fun l => Filter.Eventually.of_forall fun x => ?_
  simp only [strainAt, Nat.add_sub_cancel, (hP l).2.2]

/-- The constant of the commutator arrays. -/
def jhK (n : ℕ) (Wg aI cH w : ℝ≥0) : ℝ≥0 := 4 * 2 ^ n * (compC (invP Wg n) n * (aI * Wg)) * cH * w

/-- **Sized jets of the commutator arrays** `𝒥_H`. -/
theorem arrJetGQ_jhArr (hΛ : 1 ≤ D.Λ)
    (hP : ∀ l : CtxIdx P, l.1.2.1.WellSlotted ∧ l.1.2.1.ctxLevel = i ∧ l.1.2.1.slot = pc)
    {p' : ℤ} (hp' : IsScheduledIn D i p' pc) (n : ℕ)
    (hreg : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ n (fun y =>
      contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c))
    (hstr : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ n
      (fun x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a c))
    {cH w : ℝ≥0} (hH : ∀ a b, ctxAlgQ D bw j₀ 𝒮 i pc P X
      (fun l => covMat D (i + 1) 0 l.1.1 a b) 0 (cH * w ^ 2)) (c : Fin 2) :
    ArrJetGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ w n
      (fun l => jhArr D (i + 1) 0 l.1.1 l.1.2.1 l.1.2.2 c) 0
      (jhK n Wg (Real.toNNReal (ocA D.α D.q D.Λ i)) cH w) := by
  have hR := repAlgQ_ctxAlgQ (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := i) (pc := pc)
    (P := P) hX
  set CS := compC (invP Wg n) n * (Real.toNNReal (ocA D.α D.q D.Λ i) * Wg) with hCS
  have hS := jetRepGQ_strainAtQ (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) hX hζ hσ hWg hΛ hP hp' n hreg
  have hHj : ∀ a b, JetRepGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ n
      (fun l (_ : Vec 2) => covMat D (i + 1) 0 l.1.1 a b) 0 (cH * w ^ 2) :=
    fun a b => jetRepGQ_labelConst hR (hH a b) n
  have hMj : ∀ a b, JetRepGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ n
      (fun l x => jhMat D (i + 1) 0 l.1.1 l.1.2.1 l.1.2.2 x a b) 0
      (jhK n Wg (Real.toNNReal (ocA D.α D.q D.Λ i)) cH w * w) := by
    intro a b
    have h1 := JetRepGQ.finsetSum hR (n := n) (r := 0) Finset.univ
      (F := fun j l x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a j *
        covMat D (i + 1) 0 l.1.1 j b)
      (fun j _ l => (hstr l a j).mul contDiff_const)
      (fun j _ => JetRepGQ.mul hR (fun l => hstr l a j) (fun _ => contDiff_const) (hS a j)
        (hHj j b))
    have h2 := JetRepGQ.finsetSum hR (n := n) (r := 0) Finset.univ
      (F := fun j l x => covMat D (i + 1) 0 l.1.1 a j *
        strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x b j)
      (fun j _ l => contDiff_const.mul (hstr l b j))
      (fun j _ => JetRepGQ.mul hR (fun _ => contDiff_const) (fun l => hstr l b j) (hHj a j)
        (hS b j))
    refine ((JetRepGQ.add hR (fun l => ContDiff.sum fun j _ => (hstr l a j).mul contDiff_const)
      (fun l => ContDiff.sum fun j _ => contDiff_const.mul (hstr l b j)) h1 h2).mono hR le_rfl
      le_rfl (le_of_eq ?_)).congr_germ fun l => Filter.Eventually.of_forall fun x => ?_
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, jhK]
      push_cast
      ring
    · simp [jhMat, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have hMs : ∀ a b l, ContDiff ℝ n
      (fun x => jhMat D (i + 1) 0 (l : CtxIdx P).1.1 l.1.2.1 l.1.2.2 x a b) := by
    intro a b l
    simp only [jhMat, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact (ContDiff.sum fun j _ => (hstr l a j).mul contDiff_const).add
      (ContDiff.sum fun j _ => contDiff_const.mul (hstr l b j))
  have h := arrJetGQ_smul hR (-1) (arrJetGQ_matGradArr hR hMj hMs c)
  simp only [abs_neg, abs_one, Real.toNNReal_one, one_mul] at h
  exact h
end

/-! **Ledger, first source: the sized first-source chain.** The sized twin of the module
`GenSem.First.RepMain`.
For any sized algebra, from sized jets of the commutator arrays `𝒥_H` (constant `c_J`, order
`4p`), of the assembled mean arrays `𝓕_A = dfArr` (constant `c_F`, order `2p`) and of the
covariance entries (`|H| ≤ c_H w²`):
* `arrJetGQ_eArrQ`: the arrays of `𝒞^a 𝒥_H 𝒞^{l-1-a}`, constant `eK`;
* `arrJetGQ_wArrQ`: the arrays `wArr` of `-∑_l (1/l!) ∑_a 𝒞^a 𝒥_H 𝒞^{l-1-a} + 𝓕_A P_p`, constant
  `wK`, linear in `(c_J, c_F)`;
* `arrJetGQ_fsArrQ`: the pulled arrays `fsArr` of `Q_p wArr`, constant `fsK`.
Over the sized context calculus, with the atoms of `Diag/StrainQ`, the coefficient of tested order
`d` of the first source is a sized context function of size `fsK · w^{d-1}`
(`firstSource_ctxAlgQ`). -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

/-! ### Constants and costs -/

/-- The constant of the arrays of `𝒞^a 𝒥_H 𝒞^{l-1-a}`. -/
def eK (p : ℕ) (s cH cJ : ℝ≥0) (l a : ℕ) : ℝ≥0 :=
  compK (2 * a) (2 * p) s * (covK a (2 * p) s * cH ^ a *
    (compK 1 (2 * p + 2 * a) s * (cJ * (covK (l - 1 - a) (2 * p + 2 * a + 1) s *
      cH ^ (l - 1 - a)))))

/-- The constant of the arrays `wArr`. -/
def wK (N p : ℕ) (s cH cJ cF : ℝ≥0) : ℝ≥0 :=
  (∑ l ∈ Finset.Icc 1 p, Real.toNNReal |((l.factorial : ℝ)⁻¹)| *
      ∑ a ∈ Finset.range l, eK p s cH cJ l a) +
    compK (N + 1) (2 * p) s * (cF * polyK p wPcoef (2 * p + (N + 1)) s cH)

/-- The constant of the arrays `fsArr`. -/
def fsK (N p : ℕ) (s Wg cH cJ cF : ℝ≥0) : ℝ≥0 :=
  chartK 0 (2 * p + (N + 1 + 2 * p)) Wg
      (s + 2 ^ (0 + (2 * p + (N + 1 + 2 * p))) * invP Wg (2 * p + (N + 1 + 2 * p))) *
    (Wg * (compK (2 * p) 0 s * (polyK p wQcoef 0 s cH * wK N p s cH cJ cF)))

/-- The reserve cost of the arrays `wArr`. -/
def wR (N p rF : ℕ) : ℕ := rF + 6 * p + N + 2

/-- The reserve cost of the arrays `fsArr`. -/
def fsR (N p rF : ℕ) : ℕ := wR N p rF + 2 * p + (2 * p + (N + 1 + 2 * p))

/-! ### The chain, for any sized algebra -/

section Generic

variable {Λ : Type*} {R : (Λ → ℝ) → ℕ → ℝ≥0 → Prop} {σ w s : ℝ≥0} {D : OCData} {bw : ℝ}
  {j₀ Dm m N p : ℕ} {ρ : ℝ} {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
  {T : Finset ℤ} {cH cJ cF : ℝ≥0} {rF : ℕ}

variable (hR : RepAlgQ R) (hw : w ≠ 0) (hσ : σ * w ≤ s) (π : Λ → ℝ × RealChain × Vec 2)
  (hH : ∀ a b, R (fun l => covMat D m 0 (π l).1 a b) 0 (cH * w ^ 2))
include hR hw hσ hH

/-- **Sized arrays of `𝒞^a 𝒥_H 𝒞^{l-1-a}`.** -/
theorem arrJetGQ_eArrQ (c : Fin 2)
    (hjh : ArrJetGQ R σ w (4 * p) (fun x => jhArr D m 0 (π x).1 (π x).2.1 (π x).2.2 c) 0 cJ)
    {l a : ℕ} (hl : l ≤ p) (ha : a < l) :
    ArrJetGQ R σ w (2 * p) (fun x => eArr D m 0 (π x).1 (π x).2.1 (π x).2.2 l a c) (4 * p + 1)
      (eK p s cH cJ l a) := by
  have hin := arrJetGQ_compArr hR hw hσ (n := 2 * p + 2 * a) 1
    (hjh.mono hR (by omega) (Nat.zero_le (2 * p)) le_rfl)
    ((arrJetGQ_covArrPow hR hw hσ hH (l - 1 - a) (2 * p + 2 * a + 1)).mono hR le_rfl
      (by omega) le_rfl)
  have hout := arrJetGQ_compArr hR hw hσ (n := 2 * p) (2 * a)
    ((arrJetGQ_covArrPow hR hw hσ hH a (2 * p)).mono hR le_rfl (by omega : 0 + 2 * a ≤ 2 * p + 1)
      le_rfl) hin
  exact hout.mono hR le_rfl (by omega) le_rfl

/-- **Sized arrays `wArr`.** -/
theorem arrJetGQ_wArrQ (c : Fin 2)
    (hjh : ArrJetGQ R σ w (4 * p) (fun x => jhArr D m 0 (π x).1 (π x).2.1 (π x).2.2 c) 0 cJ)
    (hdf : ArrJetGQ R σ w (2 * p)
      (fun x => dfArr D bw j₀ Dm m ρ N Cc0 T (π x).1 (π x).2.1 (π x).2.2 c) rF cF) :
    ArrJetGQ R σ w (2 * p)
      (fun x => wArr D bw j₀ Dm m ρ N p 0 Cc0 T (π x).1 (π x).2.1 (π x).2.2 c) (wR N p rF)
      (wK N p s cH cJ cF) := by
  have he := ArrJetGQ.sum hR (Finset.Icc 1 p) fun l hl =>
    arrJetGQ_smul hR ((l.factorial : ℝ)⁻¹) (ArrJetGQ.sum hR (Finset.range l) fun a ha =>
      arrJetGQ_eArrQ hR hw hσ π hH c hjh (Finset.mem_Icc.mp hl).2 (Finset.mem_range.mp ha))
  have hc := arrJetGQ_compArr hR hw hσ (n := 2 * p) (N + 1)
    (hdf.mono hR le_rfl (Nat.le_add_right rF (2 * p)) le_rfl)
    ((arrJetGQ_polyArr hR hw hσ hH p wPcoef (2 * p + (N + 1))).mono hR le_rfl (by omega) le_rfl)
  exact ArrJetGQ.add hR ((ArrJetGQ.neg hR he).mono hR le_rfl (by unfold wR; omega) le_rfl)
    (hc.mono hR le_rfl (by unfold wR; omega) le_rfl)

/-- **Sized arrays `fsArr`**, from sized jets of the chart of the contexts. -/
theorem arrJetGQ_fsArrQ (hζ : IsFastProfile D.ζ) (hWs : ∀ x, (π x).2.1.WellSlotted) {Wg : ℝ≥0}
    (hΦj : ∀ b j, JetRepGQ R σ 0 (dLabelG j (fun x y => (π x).2.1.famMap D (π x).1 y b)) 0 Wg)
    (hIj : ∀ b j, JetRepGQ R σ (2 * p + (N + 1 + 2 * p))
      (dLabelG j (fun x y => (π x).2.1.famMapInv D (π x).1 y b)) 0
      (invP Wg (2 * p + (N + 1 + 2 * p))))
    (hMj : ∀ c k, JetRepGQ R σ 0
      (fun x y => ((jacMatrix ((π x).2.1.famMap D (π x).1) y)⁻¹) c k) 0 Wg)
    (hjh : ∀ c, ArrJetGQ R σ w (4 * p)
      (fun x => jhArr D m 0 (π x).1 (π x).2.1 (π x).2.2 c) 0 cJ)
    (hdf : ∀ c, ArrJetGQ R σ w (2 * p)
      (fun x => dfArr D bw j₀ Dm m ρ N Cc0 T (π x).1 (π x).2.1 (π x).2.2 c) rF cF) (c : Fin 2) :
    ArrJetGQ R σ w 0 (fun x => fsArr D bw j₀ Dm m ρ N p 0 Cc0 T (π x).1 (π x).2.1 (π x).2.2 c)
      (fsR N p rF) (fsK N p s Wg cH cJ cF) := by
  have hB : ∀ k, ArrJetGQ R σ w 0 (fun x => compArr (2 * p)
      (polyArr (covMat D m 0 (π x).1) p wQcoef)
      (wArr D bw j₀ Dm m ρ N p 0 Cc0 T (π x).1 (π x).2.1 (π x).2.2 k) 0) (wR N p rF + 2 * p)
      (compK (2 * p) 0 s * (polyK p wQcoef 0 s cH * wK N p s cH cJ cF)) := fun k =>
    arrJetGQ_compArr hR hw hσ (n := 0) (2 * p)
      ((arrJetGQ_polyArr hR hw hσ hH p wQcoef 0).mono hR le_rfl (by unfold wR; omega) le_rfl)
      (by rw [zero_add]; exact arrJetGQ_wArrQ hR hw hσ π hH k (hjh k) (hdf k))
  have hMs : ∀ c k x, ContDiff ℝ ((0 : ℕ) : WithTop ℕ∞)
      (fun y => ((jacMatrix ((π x).2.1.famMap D (π x).1) y)⁻¹) c k) := by
    intro c k x
    have e : (fun y => ((jacMatrix ((π x).2.1.famMap D (π x).1) y)⁻¹) c k) =
        fun y => (((π x).2.1.recenter D y).famJac D (π x).1)⁻¹ c k := by
      funext y; rw [jacMatrix_famMap hζ (π x).2.1 (hWs x) (π x).1 y]
    rw [e]
    exact (contDiff_famJacInv hζ (π x).2.1 (hWs x) (π x).1 c k).of_le (by exact_mod_cast le_top)
  exact arrJetGQ_pull hR hw hσ (n := 0) (K := 2 * p + (N + 1 + 2 * p))
    (Φ := fun x => (π x).2.1.famMap D (π x).1) (Φinv := fun x => (π x).2.1.famMapInv D (π x).1)
    (fun x => famMap_zero _ _) (fun x => (contDiff_famMap _ _).of_le (by exact_mod_cast le_top))
    (fun b j => (hΦj b j).mono hR le_rfl (Nat.zero_le _) le_rfl)
    (fun x => contDiff_famMapInv _ _)
    (fun b j => by rw [zero_add]; exact (hIj b j).mono hR le_rfl (Nat.zero_le _) le_rfl) le_rfl
    (fun c k => (hMj c k).mono hR le_rfl (Nat.zero_le _) le_rfl) hMs hB c

end Generic

/-! ### The first source over the sized context calculus -/

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {pc : ℤ}
  {P : ℝ → RealChain → Vec 2 → Prop} {X : CCtx} {σ : ℝ≥0} {Wg : ℝ≥0} {Dm N p : ℕ} {ρ : ℝ}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

/-- **The coefficients of the first source are sized context functions.** -/
theorem firstSource_ctxAlgQ (hX : X.Ok) (hζ : IsFastProfile D.ζ)
    (hσ : X.κ.Cold / ENNReal.ofReal (D.eps i * X.Δ) + ENNReal.ofReal (2 * Real.pi / D.eps i) ≤ σ)
    (hWg : ∀ L, L ≤ X.L₀ → geoW X.κ X.a L ≤ Wg) (hΛ : 1 ≤ D.Λ) {s : ℝ≥0} (hρ : 0 < ρ)
    (hσw : σ * Real.toNNReal ρ ≤ s) (hN : 1 ≤ N) (T : Finset ℤ)
    (hT : ∀ k, k ∈ T ↔ Odd k ∧ IsScheduledIn D i k pc) {p' : ℤ} (hp' : IsScheduledIn D i p' pc)
    (hP : ∀ l : CtxIdx P, l.1.2.1.WellSlotted ∧ l.1.2.1.ctxLevel = i ∧ l.1.2.1.slot = pc)
    (hSreg : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ ((4 * p : ℕ) : WithTop ℕ∞) (fun y =>
      contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c))
    (hreg : ∀ l : CtxIdx P, ∀ n, 2 ≤ n → n ≤ N + 1 → ∀ k ∈ T,
      IsAdmissibleChain D bw j₀ (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2) →
      ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
      LiftRegular (diagQ D Dm (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2) ρ)
        (Cc0 k (l.1.2.1.appendChild D k l.1.1 l.1.2.2)) (0 : Fin 1)
        ((D.cellScaleSq (i + 1))⁻¹ * l.1.1) 0 n (2 * p + Dm + 2))
    {cH : ℝ≥0} (hH : ∀ a b, ctxAlgQ D bw j₀ 𝒮 i pc P X
      (fun l => covMat D (i + 1) 0 l.1.1 a b) 0 (cH * Real.toNNReal ρ ^ 2))
    {rF : ℕ} {cF : ℝ≥0} (hdf : ∀ c, ArrJetGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ (Real.toNNReal ρ)
      (2 * p) (fun l => dfArr D bw j₀ Dm (i + 1) ρ N Cc0 T l.1.1 l.1.2.1 l.1.2.2 c) rF cF)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
    ctxAlgQ D bw j₀ 𝒮 i pc P X (fun l =>
      fluxCoeff (firstSourceFlux D bw j₀ Dm (i + 1) ρ N p 0 Cc0 l.1.1 l.1.2.1 l.1.2.2) d I 0 c)
      (fsR N p rF)
      (fsK N p s Wg cH (jhK (4 * p) Wg (Real.toNNReal (ocA D.α D.q D.Λ i)) cH (Real.toNNReal ρ))
        cF * Real.toNNReal ρ ^ (d - 1)) := by
  have hR := repAlgQ_ctxAlgQ (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := i) (pc := pc)
    (P := P) hX
  have hw : Real.toNNReal ρ ≠ 0 := (Real.toNNReal_pos.mpr hρ).ne'
  have hW : ∀ l : CtxIdx P, l.1.2.1.WellSlotted := fun l => (hP l).1
  -- the strain field in the label variable
  have hstr : ∀ l : CtxIdx P, ∀ a c', ContDiff ℝ ((4 * p : ℕ) : WithTop ℕ∞)
      (fun x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a c') := by
    intro l a c'
    have e : (fun x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a c') =
        (fun y => contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c')
          ∘ l.1.2.1.famMapInv D l.1.1 := by
      funext x
      simp only [strainAt, Function.comp_apply, Nat.add_sub_cancel, (hP l).2.2]
    have htopV : ∀ (r : ℕ) {g : Vec 2 → Vec 2}, ContDiff ℝ (⊤ : ℕ∞) g →
        ContDiff ℝ (r : WithTop ℕ∞) g := fun r _ hg => hg.of_le (by exact_mod_cast le_top)
    rw [e]
    exact (hSreg l a c').comp (htopV (4 * p) (contDiff_famMapInv _ _))
  have hjh := fun c' => arrJetGQ_jhArr (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) hX hζ hσ hWg hΛ hP hp'
    (4 * p) hSreg hstr hH c'
  have hF : ∀ c', ArrJetGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ (Real.toNNReal ρ) 0
      (fun l => fsArr D bw j₀ Dm (i + 1) ρ N p 0 Cc0 T l.1.1 l.1.2.1 l.1.2.2 c') (fsR N p rF)
      (fsK N p s Wg cH (jhK (4 * p) Wg (Real.toNNReal (ocA D.α D.q D.Λ i)) cH (Real.toNNReal ρ))
        cF) := fun c' =>
    arrJetGQ_fsArrQ hR hw hσw (fun l : CtxIdx P => (l.1.1, l.1.2.1, l.1.2.2)) hH hζ hW
      (fun b j => jetRepGQ_ctx_dLabel_famMapQ hX hζ hσ hWg hW 0 b j)
      (fun b j => jetRepGQ_ctx_dLabel_famMapInvQ hX hζ hσ hWg hW _ b j)
      (fun c k => jetRepGQ_ctx_jacInvQ hX hζ hσ hWg hW 0 c k) hjh hdf c'
  -- the extraction
  set K' := max (2 * p + (N + 1 + 2 * p)) (d - 1) with hK'
  have hA := rep_fluxCoeff_applyArrQ hR (K := K')
    (A := fun l k => fsArr D bw j₀ Dm (i + 1) ρ N p 0 Cc0 T l.1.1 l.1.2.1 l.1.2.2 k) d I
    (le_max_right _ _) c (fun m α => (hF c m α).1.value)
  have key : ∀ l : CtxIdx P,
      fluxCoeff (firstSourceFlux D bw j₀ Dm (i + 1) ρ N p 0 Cc0 l.1.1 l.1.2.1 l.1.2.2) d I 0 c =
      fluxCoeff (fun g y k => applyArr K'
        (fsArr D bw j₀ Dm (i + 1) ρ N p 0 Cc0 T l.1.1 l.1.2.1 l.1.2.2 k) g y 0) d I 0 c := by
    intro l
    have hmono : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) :=
      (contDiff_mono (0 : Vec 2) I).of_le le_top
    have hS' : ∀ k, k ∈ T ↔ Odd k ∧ IsScheduledIn D (i + 1 - 1) k l.1.2.1.slot := by
      intro k; rw [Nat.add_sub_cancel, (hP l).2.2]; exact hT k
    have hvec : firstSourceFlux D bw j₀ Dm (i + 1) ρ N p 0 Cc0 l.1.1 l.1.2.1 l.1.2.2
        (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) 0 =
        fun k => applyArr K' (fsArr D bw j₀ Dm (i + 1) ρ N p 0 Cc0 T l.1.1 l.1.2.1 l.1.2.2 k)
          (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) 0 0 := by
      refine funext fun k => ?_
      rw [firstSourceFlux_applyArr hζ hρ.ne' hN l.1.1 l.1.2.1 l.1.2.2 T hS' (hstr l) (hreg l)
        hmono 0 k, applyArr_eq_of_supp (le_max_left _ (d - 1))
        (arrSupp_fsArr _ _ _ _ _ _ _ _ _ _ _ _ _ _ k)]
    unfold fluxCoeff
    rw [hvec]
  have e : (fun l : CtxIdx P =>
      fluxCoeff (firstSourceFlux D bw j₀ Dm (i + 1) ρ N p 0 Cc0 l.1.1 l.1.2.1 l.1.2.2) d I 0 c) =
      fun l => fluxCoeff (fun g y k => applyArr K'
        (fsArr D bw j₀ Dm (i + 1) ρ N p 0 Cc0 T l.1.1 l.1.2.1 l.1.2.2 k) g y 0) d I 0 c :=
    funext key
  rw [e]
  exact hA
end

end AVRegularity.Providers.CascadeInvariants
end
