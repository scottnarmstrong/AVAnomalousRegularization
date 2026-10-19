-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.Ident
import AVRegularity.EntryTerminal.Ingredients.ScaleFacts.ScaleFacts
public import AVRegularity.CycleComparison.Coarse.Bound.AtTime
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Proofs.Transverse.ClassicalCell.Spatial
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
public import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.SpecificCodomains.Pi

section
@[expose] public noncomputable section

section
namespace AVRegularity.Construction.Residual.Presentation

/-! **The join of two flux statements at the terminal context** (shared by two flux statements).

A statement `TermResPrefix fun c x kc _ C _ _ => P c x kc C` fixes its thresholds, floors and
constants before the data it quantifies over. Two such statements about the same contexts give
one statement about the conjunction: take the maxima of `Λ₀`, `kc₀`, `S_X`, `S_Z`, `K_floor`,
`K_need`, `C₀`, `C_H`, `Υ`, `M₀`, and serve both by one carrier start (`IsCarrierStart.mono`).

Degenerate cases:
- `P₂ = P₁`: the conjunction is the statement itself.
- A statement that is true for `C ≥ C₀` stays true for the larger `max C₀ C₀'`. -/

open AVRegularity AVRegularity.EntryTerminal.Route

/-- A statement about a terminal context and the constant, with the implicit data of the context. -/
abbrev TermFluxPred : Type _ :=
  ∀ {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
    {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
    {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M), TermResAux c → ℕ → ℝ → Prop

/-- **Join of two flux statements**: the conjunction of two `TermResPrefix` statements whose
predicates ignore the reconstruction constants is again such a statement. -/
theorem termFluxPrefix_and {P₁ P₂ : TermFluxPred}
    (h₁ : TermResPrefix fun c x kc _ C _ _ => P₁ c x kc C)
    (h₂ : TermResPrefix fun c x kc _ C _ _ => P₂ c x kc C) :
    TermResPrefix fun c x kc _ C _ _ => P₁ c x kc C ∧ P₂ c x kc C := by
  intro X
  obtain ⟨Λ₁, hΛ₁, H₁⟩ := h₁ X
  obtain ⟨Λ₂, hΛ₂, H₂⟩ := h₂ X
  refine ⟨max Λ₁ Λ₂, le_trans hΛ₁ (le_max_left _ _), fun A hΛ hV => ?_⟩
  have hΛA : 128 ≤ A.Λ := le_trans hΛ₁ (le_trans (le_max_left _ _) hΛ)
  obtain ⟨hAnn, hTnn, -⟩ := scaleFacts X A.Λ hΛA
  obtain ⟨kc₁, K₁⟩ := H₁ A (le_trans (le_max_left _ _) hΛ) hV
  obtain ⟨kc₂, K₂⟩ := H₂ A (le_trans (le_max_right _ _) hΛ) hV
  refine ⟨max kc₁ kc₂, fun kc hkc => ?_⟩
  obtain ⟨SX₁, SZ₁, Kf₁, S₁⟩ := K₁ kc (le_trans (le_max_left _ _) hkc)
  obtain ⟨SX₂, SZ₂, Kf₂, S₂⟩ := K₂ kc (le_trans (le_max_right _ _) hkc)
  refine ⟨max SX₁ SX₂, max SZ₁ SZ₂, max Kf₁ Kf₂, fun sXT sZT hsX hsZ Kout hK => ?_⟩
  obtain ⟨Kn₁, N₁⟩ := S₁ sXT sZT (le_trans (le_max_left _ _) hsX) (le_trans (le_max_left _ _) hsZ)
    Kout (le_trans (le_max_left _ _) hK)
  obtain ⟨Kn₂, N₂⟩ := S₂ sXT sZT (le_trans (le_max_right _ _) hsX)
    (le_trans (le_max_right _ _) hsZ) Kout (le_trans (le_max_right _ _) hK)
  refine ⟨max Kn₁ Kn₂, ?_⟩
  intro Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0 hKs hKan hLan hJm
    cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP Cfl
  obtain ⟨C₁, cg₁, Cg₁, hcg₁, CH₁, Υ₁, hCH₁, hΥ₁, T₁⟩ := N₁ Kw Lt nW hk₀w hLw cr kS
    (le_trans (le_max_left _ _) hKn) hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0
    (le_trans (le_max_left _ _) hKs) (le_trans (le_max_left _ _) hKan)
    (le_trans (le_max_left _ _) hLan) (le_trans (le_max_left _ _) hJm)
    cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP Cfl
  obtain ⟨C₂, cg₂, Cg₂, hcg₂, CH₂, Υ₂, hCH₂, hΥ₂, T₂⟩ := N₂ Kw Lt nW hk₀w hLw cr kS
    (le_trans (le_max_right _ _) hKn) hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0
    (le_trans (le_max_right _ _) hKs) (le_trans (le_max_right _ _) hKan)
    (le_trans (le_max_right _ _) hLan) (le_trans (le_max_right _ _) hJm)
    cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP Cfl
  refine ⟨max C₁ C₂, cg₁, Cg₁, hcg₁, max CH₁ CH₂, max Υ₁ Υ₂,
    le_trans hCH₁ (le_max_left _ _), lt_of_lt_of_le hΥ₁ (le_max_left _ _), ?_⟩
  intro C hC j₀ hj₀
  obtain ⟨M₁, U₁⟩ := T₁ C (le_trans (le_max_left _ _) hC) j₀
    (IsCarrierStart.mono hAnn hTnn (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCH₁)
      hΥ₁.le hj₀)
  obtain ⟨M₂, U₂⟩ := T₂ C (le_trans (le_max_right _ _) hC) j₀
    (IsCarrierStart.mono hAnn hTnn (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCH₂)
      hΥ₂.le hj₀)
  exact ⟨max M₁ M₂, fun M hM c x =>
    ⟨U₁ M (le_trans (le_max_left _ _) hM) c x, U₂ M (le_trans (le_max_right _ _) hM) c x⟩⟩

/-- **A change of the constant**: `R` at every constant `C' ≥ C₂` follows from `P` at the constant
`C₁`, at every context with the arguments `A`. -/
def TermFluxMap {X : TermConstruction} (A : TermArgs X) (kc : ℕ) (C₁ C₂ : ℝ) (P R : TermFluxPred) :
    Prop :=
  ∀ {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+} {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts}
    {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts} {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ}
    {j₀ M : ℕ}
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c), P c x kc C₁ → ∀ C' : ℝ, C₂ ≤ C' → R c x kc C'

/-- **Relabelling the constant**: a statement `P` at every large constant gives `R` at every large
constant once `R` at `C' ≥ C₂` follows from `P` at the fixed constant `C₁`. The constant `C₂` may
depend on the arguments `A` and on `k_c`, but not on the context. -/
theorem termFluxPrefix_map {P R : TermFluxPred}
    (hmap : ∀ (X : TermConstruction) (A : TermArgs X) (kc : ℕ) (C₁ : ℝ), 128 ≤ A.Λ → 0 ≤ C₁ →
      ∃ C₂ : ℝ, TermFluxMap A kc C₁ C₂ P R)
    (h : TermResPrefix fun c x kc _ C _ _ => P c x kc C) :
    TermResPrefix fun c x kc _ C _ _ => R c x kc C := by
  intro X
  obtain ⟨Λ₁, hΛ₁, H₁⟩ := h X
  refine ⟨Λ₁, hΛ₁, fun A hΛ hV => ?_⟩
  obtain ⟨kc₁, K₁⟩ := H₁ A hΛ hV
  refine ⟨kc₁, fun kc hkc => ?_⟩
  obtain ⟨SX, SZ, Kf, S⟩ := K₁ kc hkc
  refine ⟨SX, SZ, Kf, fun sXT sZT hsX hsZ Kout hK => ?_⟩
  obtain ⟨Kn, N⟩ := S sXT sZT hsX hsZ Kout hK
  refine ⟨Kn, ?_⟩
  intro Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0 hKs hKan hLan hJm
    cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP Cfl
  obtain ⟨C₁, cg, Cg, hcg, CH, Υ, hCH, hΥ, T⟩ := N Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hKO
    hcr0 hcr1 hcr hkS hc0 hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce
    cker hcP Cfl
  obtain ⟨C₂, hC₂⟩ := hmap X A kc (max C₁ 0) (le_trans hΛ₁ hΛ) (le_max_right _ _)
  refine ⟨C₂, cg, Cg, hcg, CH, Υ, hCH, hΥ, ?_⟩
  intro C hC j₀ hj₀
  obtain ⟨M₁, U⟩ := T (max C₁ 0) (le_max_left _ _) j₀ hj₀
  exact ⟨M₁, fun M hM c x => hC₂ c x (U M hM c x) C hC⟩

/-- **Relabelling the constant, with the validity of the arguments**: as `termFluxPrefix_map`, but
the change of constant may use `A.Valid` (for instance the sign of `η₀`). -/
theorem termFluxPrefix_map_valid {P R : TermFluxPred}
    (hmap : ∀ (X : TermConstruction) (A : TermArgs X) (kc : ℕ) (C₁ : ℝ), 128 ≤ A.Λ → A.Valid →
      0 ≤ C₁ → ∃ C₂ : ℝ, TermFluxMap A kc C₁ C₂ P R)
    (h : TermResPrefix fun c x kc _ C _ _ => P c x kc C) :
    TermResPrefix fun c x kc _ C _ _ => R c x kc C := by
  intro X
  obtain ⟨Λ₁, hΛ₁, H₁⟩ := h X
  refine ⟨Λ₁, hΛ₁, fun A hΛ hV => ?_⟩
  obtain ⟨kc₁, K₁⟩ := H₁ A hΛ hV
  refine ⟨kc₁, fun kc hkc => ?_⟩
  obtain ⟨SX, SZ, Kf, S⟩ := K₁ kc hkc
  refine ⟨SX, SZ, Kf, fun sXT sZT hsX hsZ Kout hK => ?_⟩
  obtain ⟨Kn, N⟩ := S sXT sZT hsX hsZ Kout hK
  refine ⟨Kn, ?_⟩
  intro Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0 hKs hKan hLan hJm
    cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP Cfl
  obtain ⟨C₁, cg, Cg, hcg, CH, Υ, hCH, hΥ, T⟩ := N Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hKO
    hcr0 hcr1 hcr hkS hc0 hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce
    cker hcP Cfl
  obtain ⟨C₂, hC₂⟩ := hmap X A kc (max C₁ 0) (le_trans hΛ₁ hΛ) hV (le_max_right _ _)
  refine ⟨C₂, cg, Cg, hcg, CH, Υ, hCH, hΥ, ?_⟩
  intro C hC j₀ hj₀
  obtain ⟨M₁, U⟩ := T (max C₁ 0) (le_max_left _ _) j₀ hj₀
  exact ⟨M₁, fun M hM c x => hC₂ c x (U M hM c x) C hC⟩

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
namespace AVRegularity.EntryTerminal.CovOp

/-! **Realizations by formal adjoints, and continuity in a parameter**.

* `covOp_adj_value`: if `U` has the value `g` and `⟨g, Tφ⟩ = ⟨target, φ⟩` for smooth periodic `φ`,
  then `A.adj K U` has the value `target` (uniqueness of Hilbert images).
* `AdjCont A`: the adjoint maps of a family `s ↦ A s` of `TorusAdj` structures depend continuously
  (in operator norm) on the parameter. The closure lemmas follow the constructors of `Adj/Ops`,
  and the families `covOp`, `covIter`, `covPolyP`, `qpRem` built from a continuous matrix
  `H : S → Matrix` are continuous.

Degenerate cases:
- A constant family is continuous.
- `l = 0`: `covIter` is the identity, independent of the parameter. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-! ### The value of an adjoint image -/

theorem covOp_adj_value [FiniteDimensional ℝ E] {T : (Vec 2 → E) → (Vec 2 → E)} {m R Kc : ℕ} {C : ℝ}
    (A : TorusAdj T m R Kc C) {K : ℕ} (hK : K + m ≤ Kc) (U : TorusHk (K + m) E)
    {g target : Vec 2 → E} (hU : tval U =ᵐ[volume.restrict AVenhance.unitCube] g)
    (ht : Continuous target)
    (hdual : ∀ φ : Vec 2 → E, ContDiff ℝ (⊤ : ℕ∞) φ → AVenhance.IsZ2Periodic φ →
      cellInner g (T φ) = cellInner target φ) :
    tval (A.adj K hK U) =ᵐ[volume.restrict AVenhance.unitCube] target := by
  apply Construction.Preservation.FullLift.hilbert_ae_eq_of_cellInner_eq
  · exact (memLp_tval _).integrable one_le_two
  · exact (memLp_two_cell_of_continuous ht).integrable one_le_two
  · intro φ hφ hp
    rw [A.ident K hK U φ (hφ.of_le (by exact_mod_cast le_top)) hp, cellInner_congr_left hU,
      hdual φ hφ hp]

/-! ### Adjoint maps of the constructors -/

section Adj

variable {T T' : (Vec 2 → E) → (Vec 2 → E)} {m m' R Kc : ℕ} {C : ℝ}

theorem covOp_adj_ofOp (h : T = T') (A : TorusAdj T m R Kc C) (K : ℕ) (hK : K + m ≤ Kc) :
    (A.ofOp h).adj K hK = A.adj K hK := by
  subst h; rfl

theorem covOp_adj_ofOrder (h : m = m') (A : TorusAdj T m R Kc C) (K : ℕ) (hK : K + m' ≤ Kc) :
    (A.ofOrder h).adj K hK =
      (A.adj K (by omega)).comp (torusCast (by omega : K + m' = K + m)) := by
  subst h; rfl

end Adj

/-! ### Continuity in a parameter -/

section Cont

variable {S : Type*} [TopologicalSpace S]

/-- The adjoint maps of a family of structures vary continuously in operator norm. -/
def AdjCont {T : S → (Vec 2 → E) → (Vec 2 → E)} {m R Kc : ℕ} {C : S → ℝ}
    (A : ∀ s, TorusAdj (T s) m R Kc (C s)) : Prop :=
  ∀ K (hK : K + m ≤ Kc), Continuous fun s => (A s).adj K hK

section Generic

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- A family of scalar multiplications is continuous in the scalar. -/
theorem covOp_continuous_smulFamily (L : ℝ → V →L[ℝ] V) (hL : ∀ c U, L c U = c • U) :
    Continuous L := by
  have hlip : LipschitzWith 1 L := by
    refine LipschitzWith.of_dist_le_mul fun c c' => ?_
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    refine ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _) fun U => ?_
    rw [sub_apply, hL, hL, ← sub_smul, norm_smul, Real.norm_eq_abs]
  exact hlip.continuous

theorem covOp_continuous_clmSum {S ι : Type*} [TopologicalSpace S] (s : Finset ι)
    (f : ι → S → V →L[ℝ] W) (h : ∀ i, Continuous (f i)) :
    Continuous fun x => ∑ i ∈ s, f i x := continuous_finsetSum _ fun i _ => h i

theorem covOp_continuous_clmNeg {S : Type*} [TopologicalSpace S] (f : S → V →L[ℝ] W)
    (h : Continuous f) : Continuous fun x => -f x := h.neg

end Generic

theorem continuous_torusSmulCLM {K : ℕ} :
    Continuous fun c : ℝ => (torusSmulCLM c : TorusHk K E →L[ℝ] TorusHk K E) :=
  covOp_continuous_smulFamily _ fun c U => torusSmulCLM_apply c U

variable {T T' : S → (Vec 2 → E) → (Vec 2 → E)} {m m' R R' Kc Kc' : ℕ} {C C' : S → ℝ}

theorem AdjCont.const (A : TorusAdj (fun ψ : Vec 2 → E => ψ) m R Kc 0) :
    AdjCont (S := S) (fun _ => A) := fun _ _ => continuous_const

theorem AdjCont.constAny {T0 : (Vec 2 → E) → (Vec 2 → E)} {C0 : ℝ} (A : TorusAdj T0 m R Kc C0) :
    AdjCont (S := S) (fun _ => A) := fun _ _ => continuous_const

theorem AdjCont.ofOp (h : ∀ s, T s = T' s) {A : ∀ s, TorusAdj (T s) m R Kc (C s)}
    (hA : AdjCont A) : AdjCont (fun s => (A s).ofOp (h s)) := by
  intro K hK
  simp only [covOp_adj_ofOp]
  exact hA K hK

theorem AdjCont.ofOrder (h : m = m') {A : ∀ s, TorusAdj (T s) m R Kc (C s)}
    (hA : AdjCont A) : AdjCont (fun s => (A s).ofOrder h) := by
  intro K hK
  simp only [covOp_adj_ofOrder]
  exact (hA K (by omega)).clm_comp continuous_const

theorem AdjCont.mono (hR : R' ≤ R) (hKc : Kc' ≤ Kc) (hC : ∀ s, C s ≤ C' s)
    {A : ∀ s, TorusAdj (T s) m R Kc (C s)} (hA : AdjCont A) :
    AdjCont (fun s => (A s).mono hR hKc (hC s)) := fun K hK => hA K (hK.trans hKc)

theorem AdjCont.liftOrder (hm : m ≤ m') {A : ∀ s, TorusAdj (T s) m R Kc (C s)}
    (hA : AdjCont A) : AdjCont (fun s => (A s).liftOrder hm) := fun K hK =>
  (hA K (by omega)).clm_comp continuous_const

theorem AdjCont.smul (c : S → ℝ) (hc : Continuous c) {A : ∀ s, TorusAdj (T s) m R Kc (C s)}
    (hA : AdjCont A) : AdjCont (fun s => (A s).smul (c s)) := fun K hK =>
  ((continuous_torusSmulCLM.comp hc)).clm_comp (hA K hK)

theorem AdjCont.neg {A : ∀ s, TorusAdj (T s) m R Kc (C s)} (hA : AdjCont A) :
    AdjCont (fun s => (A s).neg) := fun K hK => covOp_continuous_clmNeg _ (hA K hK)

theorem AdjCont.comp {m₁ m₂ R₁ R₂ : ℕ} {T₁ T₂ : S → (Vec 2 → E) → (Vec 2 → E)} {C₁ C₂ : S → ℝ}
    {A₁ : ∀ s, TorusAdj (T₁ s) m₁ R₁ Kc (C₁ s)} {A₂ : ∀ s, TorusAdj (T₂ s) m₂ R₂ Kc (C₂ s)}
    (hA₁ : AdjCont A₁) (hA₂ : AdjCont A₂) (hR₁ : R ≤ R₁) (hR₂ : R + m₁ ≤ R₂) :
    AdjCont (fun s => (A₁ s).comp (A₂ s) hR₁ hR₂) := fun K hK =>
  (hA₂ K (by omega)).clm_comp ((hA₁ (K + m₂) (by omega)).clm_comp continuous_const)

theorem AdjCont.sum {ι : Type*} (s0 : Finset ι) {T : S → ι → (Vec 2 → E) → (Vec 2 → E)}
    {C : S → ι → ℝ} {A : ∀ s, ∀ i, TorusAdj (T s i) m R Kc (C s i)}
    (hA : ∀ i, AdjCont (fun s => A s i)) :
    AdjCont (fun s => TorusAdj.sum s0 (A s)) := fun K hK =>
  covOp_continuous_clmSum _ _ fun i => hA i K hK

theorem covOp_adj_sumMem {ι : Type*} (s0 : Finset ι) {T : ι → (Vec 2 → E) → (Vec 2 → E)}
    {C : ι → ℝ} (A : ∀ i ∈ s0, TorusAdj (T i) m R Kc (C i)) (K : ℕ) (hK : K + m ≤ Kc) :
    (TorusAdj.sumMem s0 A).adj K hK = ∑ i : s0, (A i.1 i.2).adj K hK := by
  unfold TorusAdj.sumMem
  rw [covOp_adj_ofOp]
  rfl

theorem AdjCont.sumMem {ι : Type*} (s0 : Finset ι) {T : S → ι → (Vec 2 → E) → (Vec 2 → E)}
    {C : S → ι → ℝ} {A : ∀ s, ∀ i ∈ s0, TorusAdj (T s i) m R Kc (C s i)}
    (hA : ∀ i hi, AdjCont (fun s => A s i hi)) :
    AdjCont (fun s => TorusAdj.sumMem s0 (A s)) := by
  intro K hK
  simp only [covOp_adj_sumMem]
  exact covOp_continuous_clmSum _ (fun (i : s0) x => (A x i.1 i.2).adj K hK) fun i => hA i.1 i.2 K hK

end Cont

/-! ### The structures built from a continuous matrix family -/

section Poly

variable [FiniteDimensional ℝ E] {S : Type*} [TopologicalSpace S]
  {H : S → Matrix (Fin 2) (Fin 2) ℝ} {M : ℝ}

theorem covOp_adjCont_covOp (hH : Continuous H) (hM : ∀ s, covBound (H s) ≤ M) (R Kc : ℕ) :
    AdjCont (fun s => TorusAdj.covOp (E := E) (H s) (hM s) R Kc) := by
  intro K hK
  have key : (fun s => (TorusAdj.covOp (E := E) (H s) (hM s) R Kc).adj K hK) = fun s =>
      ∑ i : Fin 2, ∑ j : Fin 2, (torusSmulCLM (H s i j)).comp
        ((TorusAdj.secondDeriv (E := E) i j R Kc).adj K hK) := by
    funext s
    unfold TorusAdj.covOp
    rw [covOp_adj_ofOp]
    rfl
  rw [key]
  refine covOp_continuous_clmSum _ _ fun i => covOp_continuous_clmSum _ _ fun j => ?_
  exact (continuous_torusSmulCLM.comp (hH.matrix_elem i j)).clm_comp continuous_const

theorem covOp_adjCont_covIter (hH : Continuous H) (hM : ∀ s, covBound (H s) ≤ M) :
    ∀ (l R Kc : ℕ), AdjCont (fun s => TorusAdj.covIter (E := E) (H s) (hM s) l R Kc)
  | 0, R, Kc => by
    intro K hK
    simp only [TorusAdj.covIter]
    exact continuous_const
  | l + 1, R, Kc => by
    simp only [TorusAdj.covIter]
    exact AdjCont.ofOp _ (AdjCont.ofOrder _ (AdjCont.mono _ _ _
      (AdjCont.comp (covOp_adjCont_covOp hH hM R Kc) (covOp_adjCont_covIter hH hM l (R + 2) Kc)
        _ _)))

theorem covOp_adjCont_covPolyP (hH : Continuous H) (hM : ∀ s, covBound (H s) ≤ M)
    (p R Kc : ℕ) :
    AdjCont (fun s => TorusAdj.covPolyP (E := E) (H s) (hM s) p R Kc) := by
  unfold TorusAdj.covPolyP
  exact AdjCont.ofOp _ (AdjCont.mono _ _ _ (AdjCont.sumMem _ fun l hl =>
    AdjCont.smul (fun _ => _) continuous_const
      (AdjCont.liftOrder _ (covOp_adjCont_covIter hH hM l R Kc))))

theorem covOp_adjCont_qpRemTerm (hH : Continuous H) (hM : ∀ s, covBound (H s) ≤ M)
    (p R Kc a b : ℕ) (ha : a < p + 1) (hb : b < p + 1) :
    AdjCont (fun s => TorusAdj.qpRemTerm (E := E) (H s) (hM s) p R Kc a b ha hb) := by
  unfold TorusAdj.qpRemTerm
  exact AdjCont.smul (fun _ => _) continuous_const
    (AdjCont.liftOrder _ (covOp_adjCont_covIter hH hM (a + b) R Kc))

theorem covOp_adjCont_qpRem (hH : Continuous H) (hM : ∀ s, covBound (H s) ≤ M)
    (p R Kc : ℕ) :
    AdjCont (fun s => TorusAdj.qpRem (E := E) (H s) (hM s) p R Kc) := by
  unfold TorusAdj.qpRem
  exact AdjCont.neg (AdjCont.ofOp _ (AdjCont.mono _ _ _ (AdjCont.sumMem _ fun a ha =>
    AdjCont.sumMem _ fun b hb =>
      covOp_adjCont_qpRemTerm hH hM p R Kc a b (Finset.mem_range.mp ha)
        (Finset.mem_range.mp hb))))

end Poly

end AVRegularity.EntryTerminal.CovOp
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
open AVRegularity.CoupledEnergy.Variational AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.CovOp

/-! **A formal adjoint realizes the transformed flux, with the factorial-norm price**.

For a family `s ↦ A v s` of `TorusAdj` structures over the window `I` (continuous in `s`, norm
bounded, factorial-norm price `Cb`), a flux `F` with a realization of order `k + m` and a target
flux `target` dual to it (`⟨F, T φ⟩ = ⟨target, φ⟩` for smooth periodic `φ`), the target has a
realization of order `k` with the mass of `F` times `Cb`: `Fk ↦ A.adj k (Fk)`. The time
measurability of the new trajectory is the continuity of the adjoint maps in `s`.

Degenerate cases:
- `Cb = 0`: the target is realized by `0`.
- `m = 0`, `A.adj = id`: nothing changes. -/

open scoped Classical in
/-- A continuous family of bounded operators applied to a measurable trajectory is measurable on a
measurable window (set to `0` outside it). -/
theorem covOp_aesm_apply {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {I : Set ℝ} (hI : MeasurableSet I)
    (Ad : ↥I → V →L[ℝ] W) (hAd : Continuous Ad) {U : ℝ → V}
    (hU : AEStronglyMeasurable U (volume.restrict I)) :
    AEStronglyMeasurable (fun t => if ht : t ∈ I then Ad ⟨t, ht⟩ (U t) else 0)
      (volume.restrict I) := by
  let Ad' : ℝ → V →L[ℝ] W := fun t => if ht : t ∈ I then Ad ⟨t, ht⟩ else 0
  have hc : ContinuousOn Ad' I := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : I.domRestrict Ad' = Ad := by
      funext t; simp [Set.domRestrict, Ad', t.2]
    rw [this]; exact hAd
  have h1 : AEStronglyMeasurable Ad' (volume.restrict I) := hc.aestronglyMeasurable hI
  have h2 := (ContinuousLinearMap.id ℝ (V →L[ℝ] W)).aestronglyMeasurable_comp₂ h1 hU
  refine h2.congr (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ I <;> simp [Ad', ht]

theorem covOp_sq_le_of_sqrt_le {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : Real.sqrt a ≤ C * Real.sqrt b) : a ≤ C ^ 2 * b := by
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt ha, mul_pow, Real.sq_sqrt hb] at h2
  exact h2

theorem covOp_sqrt_scale_le {ν I1 J Cb Y : ℝ} (hν : 0 < ν) (hCb : 0 ≤ Cb) (hI : I1 ≤ Cb ^ 2 * J)
    (hJ : Real.sqrt (ν⁻¹ * J) ≤ Y) : Real.sqrt (ν⁻¹ * I1) ≤ Cb * Y := by
  calc Real.sqrt (ν⁻¹ * I1) ≤ Real.sqrt (ν⁻¹ * (Cb ^ 2 * J)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hI (inv_pos.2 hν).le)
    _ = Cb * Real.sqrt (ν⁻¹ * J) := by
        rw [show ν⁻¹ * (Cb ^ 2 * J) = Cb ^ 2 * (ν⁻¹ * J) by ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hCb]
    _ ≤ Cb * Y := mul_le_mul_of_nonneg_left hJ hCb

section Flux

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The mass of a measurable square integrable trajectory family is integrable. -/
theorem covOp_mass_integrable {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ)
    (G : ∀ v : ι, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
    (hG : ∀ v, MemLp (G v) 2 (volume.restrict I)) :
    Integrable (fun s => massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
      (K := K) ρ π (fun v => (G v s).val)) (volume.restrict I) := by
  have h1 : MemLp (fun s => fun v => G v s) 2 (volume.restrict I) := memLp_pi_iff.mpr hG
  have h2 := (massWeightedCarrierCLM (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
    K ρ π).comp_memLp' h1
  refine (h2.norm.integrable_sq).congr (Filter.Eventually.of_forall fun s => ?_)
  exact massWeightedCarrierCLM_normSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
    K ρ π hπ (fun v => G v s)

theorem covOp_mass_pointwise {K K' : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (Cb : ℝ)
    (G₁ : ∀ v : ι, TorusHk (K' v) (PiLp 2 (fun _ : Fin 2 => h v)))
    (G₂ : ∀ v : ι, TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
    (hv : ∀ v, factorialNormSq ρ (G₁ v).val ≤ Cb ^ 2 * factorialNormSq ρ (G₂ v).val) :
    massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v)) (K := K') ρ π
        (fun v => (G₁ v).val) ≤
      Cb ^ 2 * massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
        (K := K) ρ π (fun v => (G₂ v).val) := by
  unfold massNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have hπ' : 0 ≤ (π v)⁻¹ := (inv_pos.2 (hπ v)).le
  calc (π v)⁻¹ * factorialNormSq ρ (G₁ v).val
      ≤ (π v)⁻¹ * (Cb ^ 2 * factorialNormSq ρ (G₂ v).val) :=
        mul_le_mul_of_nonneg_left (hv v) hπ'
    _ = Cb ^ 2 * ((π v)⁻¹ * factorialNormSq ρ (G₂ v).val) := by ring

/-- The mass bound of a transformed trajectory family from a pointwise factorial-norm bound. -/
theorem covOp_fluxMassLe_of_comparison {K K' : ι → ℕ} (I : Set ℝ) (hI : MeasurableSet I)
    (ν ρ : ℝ) (π : ι → ℝ) (hν : 0 < ν) (hπ : ∀ v, 0 < π v) {Y Cn Cb : ℝ} (hCb : 0 ≤ Cb)
    (Fk : ∀ v : ι, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
    (W : ∀ v : ι, ℝ → TorusHk (K' v) (PiLp 2 (fun _ : Fin 2 => h v)))
    (hmass : FluxMassLe (K := K) ν ρ π I Fk Y)
    (hmeas : ∀ v, AEStronglyMeasurable (W v) (volume.restrict I))
    (hnorm : ∀ v, ∀ t ∈ I, ‖W v t‖ ≤ Cn * ‖Fk v t‖)
    (hfn : ∀ v, ∀ t ∈ I,
      factorialNormSq ρ (W v t).val ≤ Cb ^ 2 * factorialNormSq ρ (Fk v t).val) :
    FluxMassLe (K := K') ν ρ π I W (Cb * Y) := by
  have hmem : ∀ v, MemLp (W v) 2 (volume.restrict I) := fun v =>
    (hmass.1 v).of_le_mul (hmeas v) (ae_restrict_of_forall_mem hI (hnorm v))
  refine ⟨hmem, ?_⟩
  have hint1 := covOp_mass_integrable (h := h) ρ π hπ I W hmem
  have hint2 := covOp_mass_integrable (h := h) ρ π hπ I Fk hmass.1
  have hpt : ∀ s ∈ I, massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
      (K := K') ρ π (fun v => (W v s).val) ≤
      Cb ^ 2 * massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
        (K := K) ρ π (fun v => (Fk v s).val) := fun s hs =>
    covOp_mass_pointwise ρ π hπ Cb (fun v => W v s) (fun v => Fk v s) fun v => hfn v s hs
  refine covOp_sqrt_scale_le hν hCb ?_ hmass.2
  rw [← integral_const_mul]
  exact integral_mono_ae hint1 (hint2.const_mul _) (ae_restrict_of_forall_mem hI hpt)

section Adjoint

variable {k m : ℕ} {I : Set ℝ}
  {T : ∀ v : ι, ↥I → (Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) →
    (Vec 2 → PiLp 2 (fun _ : Fin 2 => h v))} {Cn : ℝ}

omit [Fintype ι] in
/-- The transformed trajectory: the adjoint maps applied to a measurable trajectory. -/
theorem covOp_traj (hI : MeasurableSet I) (A : ∀ v (s : ↥I), TorusAdj (T v s) m k (k + m) Cn)
    (hA : ∀ v, AdjCont (A v))
    (Fk : ∀ v : ι, ℝ → TorusHk (k + m) (PiLp 2 (fun _ : Fin 2 => h v)))
    (hFk : ∀ v, AEStronglyMeasurable (Fk v) (volume.restrict I)) :
    ∃ W : ∀ v : ι, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)),
      (∀ v, ∀ t (ht : t ∈ I), W v t = (A v ⟨t, ht⟩).adj k le_rfl (Fk v t)) ∧
      ∀ v, AEStronglyMeasurable (W v) (volume.restrict I) := by
  classical
  refine ⟨fun v t => if ht : t ∈ I then (A v ⟨t, ht⟩).adj k le_rfl (Fk v t) else 0,
    fun v t ht => by simp [ht], fun v => ?_⟩
  exact covOp_aesm_apply hI _ (hA v k le_rfl) (hFk v)

omit [Fintype ι] in
theorem covOp_traj_bounds (A : ∀ v (s : ↥I), TorusAdj (T v s) m k (k + m) Cn) {ρ Cb : ℝ}
    (hFB : ∀ v s, (A v s).FBound ρ Cb)
    (Fk : ∀ v : ι, ℝ → TorusHk (k + m) (PiLp 2 (fun _ : Fin 2 => h v)))
    (W : ∀ v : ι, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (hWI : ∀ v, ∀ t (ht : t ∈ I), W v t = (A v ⟨t, ht⟩).adj k le_rfl (Fk v t)) :
    (∀ v, ∀ t ∈ I, ‖W v t‖ ≤ Cn * ‖Fk v t‖) ∧ ∀ v, ∀ t ∈ I,
      factorialNormSq ρ (W v t).val ≤ Cb ^ 2 * factorialNormSq ρ (Fk v t).val := by
  refine ⟨fun v t ht => ?_, fun v t ht => ?_⟩
  · rw [hWI v t ht]
    exact ((A v ⟨t, ht⟩).adj k le_rfl).le_opNorm _ |>.trans
      (mul_le_mul_of_nonneg_right ((A v ⟨t, ht⟩).bound k le_rfl) (norm_nonneg _))
  · have hv := hFB v ⟨t, ht⟩ k le_rfl (Fk v t)
    rw [← hWI v t ht] at hv
    exact covOp_sq_le_of_sqrt_le (factorialNormSq_nonneg _ _) (factorialNormSq_nonneg _ _) hv

omit [Fintype ι] in
theorem covOp_traj_realizes (A : ∀ v (s : ↥I), TorusAdj (T v s) m k (k + m) Cn)
    (Fk : ∀ v : ι, ℝ → TorusHk (k + m) (PiLp 2 (fun _ : Fin 2 => h v)))
    (W : ∀ v : ι, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (hWI : ∀ v, ∀ t (ht : t ∈ I), W v t = (A v ⟨t, ht⟩).adj k le_rfl (Fk v t))
    (F target : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v))
    (hr : IsFluxRealization (k + m) I F Fk)
    (htc : ∀ v, ∀ t ∈ I, Continuous (target v t))
    (hdual : ∀ v (t : ℝ) (ht : t ∈ I) (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)),
      ContDiff ℝ (⊤ : ℕ∞) φ → AVenhance.IsZ2Periodic φ →
      cellInner (F v t) (T v ⟨t, ht⟩ φ) = cellInner (target v t) φ) :
    IsFluxRealization k I target W := by
  intro v t ht
  rw [hWI v t ht]
  exact covOp_adj_value (A v ⟨t, ht⟩) le_rfl (Fk v t) (hr v t ht) (htc v t ht) (hdual v t ht)

/-- **The realization by adjoint maps.** -/
theorem covOp_fluxBound_of_adj (hI : MeasurableSet I) (ν ρ : ℝ)
    (π : ι → ℝ) (hν : 0 < ν) (hπ : ∀ v, 0 < π v)
    (A : ∀ v (s : ↥I), TorusAdj (T v s) m k (k + m) Cn)
    (hA : ∀ v, AdjCont (A v)) (Cb : ℝ) (hCb : 0 ≤ Cb) (hFB : ∀ v s, (A v s).FBound ρ Cb)
    (F target : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) (Y : ℝ)
    (hF : HasFluxBound (k + m) I ν ρ π F Y)
    (htc : ∀ v, ∀ t ∈ I, Continuous (target v t))
    (hdual : ∀ v (t : ℝ) (ht : t ∈ I) (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)),
      ContDiff ℝ (⊤ : ℕ∞) φ → AVenhance.IsZ2Periodic φ →
      cellInner (F v t) (T v ⟨t, ht⟩ φ) = cellInner (target v t) φ) :
    HasFluxBound k I ν ρ π target (Cb * Y) := by
  obtain ⟨Fk, hr, hmass⟩ := hF
  obtain ⟨W, hWI, hmeas⟩ := covOp_traj hI A hA Fk (fun v => (hmass.1 v).aestronglyMeasurable)
  obtain ⟨hnorm, hfn⟩ := covOp_traj_bounds A hFB Fk W hWI
  exact ⟨W, covOp_traj_realizes A Fk W hWI F target hr htc hdual,
    covOp_fluxMassLe_of_comparison (K := fun _ => k + m) (K' := fun _ => k) I hI ν ρ π hν hπ
      hCb Fk W hmass hmeas hnorm hfn⟩

end Adjoint

end Flux

end AVRegularity.EntryTerminal.CovOp
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.EntryTerminal.CovOp
namespace AVRegularity.Construction.Residual.Presentation

/-! Exact flux operators on a finite family of gradient carriers. The ordinary operator
bound is used only for time integrability. The weighted bound, which includes mixing between
components, supplies the quantitative mass price. This avoids a componentwise estimate that
would lose the Schur bound when the number of components grows.

Degenerate cases: the empty family has zero mass; the identity operator has price one; the zero
operator has price zero; shrinking the window does not introduce a duration factor. -/

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- A time-dependent operator with its exact classical action and a mass-weighted price.
Its ordinary norm bound need not be uniform in the component set; its mass price must be. -/
structure CovTruncFluxOperator (Kin K : ℕ) (I : Set ℝ) (ρ : ℝ) (π : ι → ℝ) (Cb : ℝ)
    (input target : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) where
  op : ℝ → ((∀ v, TorusHk Kin (PiLp 2 (fun _ : Fin 2 => h v))) →L[ℝ]
    (∀ v, TorusHk K (PiLp 2 (fun _ : Fin 2 => h v))))
  norm_bound : ∃ Cn : ℝ, ∀ t ∈ I, ‖op t‖ ≤ Cn
  measurable_apply : ∀ U : ∀ v, ℝ → TorusHk Kin (PiLp 2 (fun _ : Fin 2 => h v)),
    (∀ v, AEStronglyMeasurable (U v) (volume.restrict I)) → ∀ v,
      AEStronglyMeasurable (fun t => op t (fun u => U u t) v) (volume.restrict I)
  weighted_bound : ∀ t ∈ I, ∀ U,
    massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => K) ρ π
      (fun v => (op t U v).val) ≤ Cb ^ 2 *
        massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => Kin) ρ π
          (fun v => (U v).val)
  realizes : ∀ U : ∀ v, ℝ → TorusHk Kin (PiLp 2 (fun _ : Fin 2 => h v)),
    IsFluxRealization Kin I input U →
      IsFluxRealization K I target (fun v t => op t (fun u => U u t) v)

private theorem covTruncOperator_apply_memLp {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {κ : Type*} [Fintype κ] {W : κ → Type*}
    [∀ v, NormedAddCommGroup (W v)] [∀ v, NormedSpace ℝ (W v)]
    {I : Set ℝ} (hI : MeasurableSet I) (T : ℝ → V →L[ℝ] (∀ v, W v))
    (U : ℝ → V) (hU : MemLp U 2 (volume.restrict I)) (Cn : ℝ)
    (hCn : ∀ t ∈ I, ‖T t‖ ≤ Cn)
    (hm : ∀ v, AEStronglyMeasurable (fun t => T t (U t) v) (volume.restrict I)) :
    ∀ v, MemLp (fun t => T t (U t) v) 2 (volume.restrict I) := by
  intro v
  refine hU.of_le_mul (c := Cn) (hm v) (ae_restrict_of_forall_mem hI fun t ht => ?_)
  exact (norm_le_pi_norm (T t (U t)) v).trans
    (((T t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hCn t ht) (norm_nonneg _)))

private theorem covTruncOperator_mass_bound {Kin K : ℕ} {I : Set ℝ}
    (hI : MeasurableSet I) {ν ρ Cb Y : ℝ} {π : ι → ℝ} (hν : 0 < ν)
    (hπ : ∀ v, 0 < π v) (hCb : 0 ≤ Cb)
    (U : ∀ v, ℝ → TorusHk Kin (PiLp 2 (fun _ : Fin 2 => h v)))
    (W : ∀ v, ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => h v)))
    (hm : FluxMassLe (ι := ι) (h := h) (K := fun _ => Kin) ν ρ π I U Y)
    (hW : ∀ v, MemLp (W v) 2 (volume.restrict I))
    (hpt : ∀ t ∈ I,
      massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => K) ρ π
        (fun v => (W v t).val) ≤ Cb ^ 2 *
          massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => Kin) ρ π
            (fun v => (U v t).val)) :
    FluxMassLe (ι := ι) (h := h) (K := fun _ => K) ν ρ π I W (Cb * Y) := by
  refine ⟨hW, ?_⟩
  have hiW := covOp_mass_integrable (ι := ι) (h := h) (K := fun _ => K) ρ π hπ I W hW
  have hiU := covOp_mass_integrable (ι := ι) (h := h) (K := fun _ => Kin) ρ π hπ I U hm.1
  apply covOp_sqrt_scale_le hν hCb _ hm.2
  rw [← integral_const_mul]
  exact integral_mono_ae hiW (hiU.const_mul _) (ae_restrict_of_forall_mem hI hpt)

/-- The action of an exact flux operator on a family of time trajectories. -/
def CovTruncFluxOperator.applyTo {Kin K : ℕ} {I : Set ℝ} {ρ Cb : ℝ} {π : ι → ℝ}
    {input target : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)}
    (P : CovTruncFluxOperator (ι := ι) (h := h) Kin K I ρ π Cb input target)
    (U : ∀ v, ℝ → TorusHk Kin (PiLp 2 (fun _ : Fin 2 => h v))) :
    ∀ v, ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => h v)) :=
  fun v t => P.op t (fun u => U u t) v

/-- A uniformly bounded operator with measurable action preserves square integrability. -/
theorem CovTruncFluxOperator.applyTo_memLp {Kin K : ℕ} {I : Set ℝ}
    (hI : MeasurableSet I) {ρ Cb : ℝ} {π : ι → ℝ}
    {input target : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)}
    (P : CovTruncFluxOperator (ι := ι) (h := h) Kin K I ρ π Cb input target)
    (U : ∀ v, ℝ → TorusHk Kin (PiLp 2 (fun _ : Fin 2 => h v)))
    (hU : ∀ v, MemLp (U v) 2 (volume.restrict I)) :
    ∀ v, MemLp (P.applyTo U v) 2 (volume.restrict I) := by
  have hm := P.measurable_apply U (fun v => (hU v).aestronglyMeasurable)
  obtain ⟨Cn, hCn⟩ := P.norm_bound
  exact covTruncOperator_apply_memLp hI P.op (fun t v => U v t)
    (memLp_pi_iff.mpr hU) Cn hCn hm

/-- The mass-weighted operator bound transfers the square-integrable flux price. -/
theorem CovTruncFluxOperator.applyTo_mass {Kin K : ℕ} {I : Set ℝ} (hI : MeasurableSet I)
    {ν ρ Cb Y : ℝ} {π : ι → ℝ} (hν : 0 < ν) (hπ : ∀ v, 0 < π v) (hCb : 0 ≤ Cb)
    {input target : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)}
    (P : CovTruncFluxOperator (ι := ι) (h := h) Kin K I ρ π Cb input target)
    (U : ∀ v, ℝ → TorusHk Kin (PiLp 2 (fun _ : Fin 2 => h v)))
    (hU : FluxMassLe (ι := ι) (h := h) (K := fun _ => Kin) ν ρ π I U Y) :
    FluxMassLe (ι := ι) (h := h) (K := fun _ => K) ν ρ π I (P.applyTo U) (Cb * Y) := by
  exact covTruncOperator_mass_bound (ι := ι) (h := h) hI hν hπ hCb U (P.applyTo U)
    hU (P.applyTo_memLp hI U hU.1) (fun t ht => P.weighted_bound t ht (fun u => U u t))

/-- The exact realization and the weighted operator bound transfer a flux mass estimate. -/
theorem CovTruncFluxOperator.hasFluxBound {Kin K : ℕ} {I : Set ℝ} (hI : MeasurableSet I)
    {ν ρ Cb Y : ℝ} {π : ι → ℝ} (hν : 0 < ν) (hπ : ∀ v, 0 < π v) (hCb : 0 ≤ Cb)
    {input target : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)}
    (P : CovTruncFluxOperator (ι := ι) (h := h) Kin K I ρ π Cb input target)
    (hinput : HasFluxBound (ι := ι) (h := h) Kin I ν ρ π input Y) :
    HasFluxBound (ι := ι) (h := h) K I ν ρ π target (Cb * Y) := by
  obtain ⟨U, hr, hm⟩ := hinput
  exact ⟨P.applyTo U, P.realizes U hr, P.applyTo_mass hI hν hπ hCb U hm⟩

/-- Exact operators compose without losing the finite-family mass weighting. -/
def CovTruncFluxOperator.comp {Kin J K : ℕ} {I : Set ℝ} {ρ C₁ C₂ : ℝ} {π : ι → ℝ}
    {input middle target : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)}
    (P : CovTruncFluxOperator (h := h) Kin J I ρ π C₁ input middle)
    (Q : CovTruncFluxOperator (h := h) J K I ρ π C₂ middle target) :
    CovTruncFluxOperator (h := h) Kin K I ρ π (C₂ * C₁) input target := by
  refine {
    op := fun t => (Q.op t).comp (P.op t)
    norm_bound := ?_
    measurable_apply := fun U hU v => ?_
    weighted_bound := fun t ht U => ?_
    realizes := fun U hU => Q.realizes (P.applyTo U) (P.realizes U hU) }
  · obtain ⟨Cn₁, hn₁⟩ := P.norm_bound
    obtain ⟨Cn₂, hn₂⟩ := Q.norm_bound
    refine ⟨max Cn₂ 0 * max Cn₁ 0, fun t ht => ?_⟩
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul ((hn₂ t ht).trans (le_max_left _ _))
      ((hn₁ t ht).trans (le_max_left _ _)) (norm_nonneg _) (le_max_right _ _)
  · exact Q.measurable_apply (P.applyTo U) (P.measurable_apply U hU) v
  · refine (Q.weighted_bound t ht (P.op t U)).trans ?_
    calc
      _ ≤ C₂ ^ 2 * (C₁ ^ 2 * massNormSq
          (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => Kin)
          ρ π (fun v => (U v).val)) :=
        mul_le_mul_of_nonneg_left (P.weighted_bound t ht U) (sq_nonneg _)
      _ = _ := by ring

end AVRegularity.Construction.Residual.Presentation
end
end
