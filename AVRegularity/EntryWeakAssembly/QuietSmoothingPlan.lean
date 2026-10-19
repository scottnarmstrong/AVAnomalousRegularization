-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.QuietPassageRows
public import AVRegularity.EntryWeakAssembly.QuietScalarPathPrice
public import AVRegularity.Proofs.WeakGen.Comparison.RowCoefficients
import AVRegularity.CycleJoint.PeriodicOperatorImageBudget

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleComparison.Coarse
open AVRegularity.Providers.WeakGen.Comparison
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Production of the actual aggregate signed insertion from the parent
coefficient matrix. Constituent prices sum against b; no component count,
identity count, or ambient cap enters the common price. -/

local instance quietSourceInsertionTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
local instance quietSourceInsertionTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
local instance quietSourceInsertionTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance
variable {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}

/-- Exactly the physical identities and nonzero weak differential orders. -/
abbrev WeakQuietSourceIndex (x : WeakQuietExpansionCase plan prices) (v u : x.Vertex) :=
  Σ _γ : (x.c.stage x.i).fam.Γ v u, ↥(Finset.Icc 2 x.order)

/-- Each actual constituent satisfies the proved single-source premises. -/
abbrev weakQuietConstituentContext (hok : WeakQuietRowsPlanOK plan prices)
    (x : WeakQuietExpansionCase plan prices) (v u : x.Vertex) (k : WeakQuietSourceIndex x v u) :
    WeakQuietSourceContext where
  ν := x.c.D.κ x.c.M
  ε := x.c.D.eps (x.i - 1)
  c := plan.radius x.R
  a := x.left
  b := x.right
  β := weakQuietCoefficientWeight x v u k.1 k.2.1
  r := k.2.1 - 1
  m := x.order
  cap := x.cap
  J := plan.jetOrder x.R
  ν_pos := x.bounds.2.1
  ε_pos := x.bounds.1
  c_pos := plan.radius_pos x.R
  c_small := by have h := hok.small x.R; linarith only [h]
  β_nonneg := weak_quiet_coefficient_weight_nonneg x v u k.1 k.2.1
  r_pos := by have := (Finset.mem_Icc.mp k.2.2).1; omega
  order_le := by have := Finset.mem_Icc.mp k.2.2; omega
  cap_ge := by
    have hd := (hok.depth x.R).1
    have hd1 : 1 ≤ prices.depth x.R := by omega
    have hm : x.order ≤ prices.depth x.R * x.order := by
      simpa only [one_mul] using Nat.mul_le_mul_right x.order hd1
    exact hm.trans (Nat.le_add_left _ _)
  jets := (hok.depth x.R).2
  coeff := (x.c.stage x.i).physCoeff v u k.1 k.2.1
  finite := x.coefficient_finite v u k.1 k.2.1 (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp k.2.2).1, (Finset.mem_Icc.mp k.2.2).2.trans x.c.order_ge⟩)
  budget := by
    simpa only [Nat.sub_sub] using
      (weak_quiet_coefficient_weight_identity x v u k.1 k.2.1).symm.le
  measurable := (weakPassage_physCoeff_regular x.c ((hok.coeff x.R x.c.j₀).trans x.c.level_ge)
    x.i x.level_lt x.level_le x.left x.right v u k.1 k.2.1 (Finset.mem_Icc.mp k.2.2).1).1
  smooth := x.bounds.2.2.2.2.2.2.2.1 v u k.1 k.2.1
    (Finset.mem_Icc.mp k.2.2).1 ((Finset.mem_Icc.mp k.2.2).2.trans x.c.order_ge)
  periodic := fun t _ => (weakPassage_physCoeff_regular x.c ((hok.coeff x.R x.c.j₀).trans x.c.level_ge)
    x.i x.level_lt x.level_le x.left x.right v u k.1 k.2.1 (Finset.mem_Icc.mp k.2.2).1).2.2.1 t

/-- Sum the genuine constituents to recover the complete physical source. -/
theorem weak_quiet_source_index_sum (x : WeakQuietExpansionCase plan prices)
    (v u : x.Vertex) (t : ℝ) (ψ : Vec 2 → ℝ) (y : Vec 2) :
    Real.sqrt (x.mass u / x.mass v) *
      (∑ k : WeakQuietSourceIndex x v u,
        weakQuietPrimalSource (k.2.1 - 1) ((x.c.stage x.i).physCoeff v u k.1 k.2.1 t) ψ y) =
      x.source v u t ψ y := by
  rw [x.source_orders]
  congr 1
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro γ _
  exact Finset.sum_coe_sort (Finset.Icc 2 x.order) (fun d : ℕ =>
    weakQuietPrimalSource (d - 1) ((x.c.stage x.i).physCoeff v u γ d t) ψ y)

/-- The rates of all native constituents have exactly the b-entry budget. -/
theorem weak_quiet_constituent_rates (hok : WeakQuietRowsPlanOK plan prices)
    (x : WeakQuietExpansionCase plan prices) (v u : x.Vertex) :
    Real.sqrt (x.mass u / x.mass v) *
      (∑ k : WeakQuietSourceIndex x v u, (weakQuietConstituentContext hok x v u k).rate) ≤
      x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice * x.b v u := by
  have he : (∑ k : WeakQuietSourceIndex x v u,
      (weakQuietConstituentContext hok x v u k).rate) =
      (x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice) *
        ∑ γ : (x.c.stage x.i).fam.Γ v u, ∑ d ∈ Finset.Icc 2 x.order,
          weakQuietCoefficientWeight x v u γ d := by
    dsimp only [WeakQuietSourceContext.rate, WeakQuietSourceContext.price, weakQuietConstituentContext]
    rw [← Finset.mul_sum, Fintype.sum_sigma]
    congr 1
    apply Finset.sum_congr rfl
    intro γ _
    exact Finset.sum_coe_sort (Finset.Icc 2 x.order)
      (fun d : ℕ => weakQuietCoefficientWeight x v u γ d)
  rw [he]
  calc
    _ = (x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice) *
        (Real.sqrt (x.mass u / x.mass v) *
          ∑ γ : (x.c.stage x.i).fam.Γ v u, ∑ d ∈ Finset.Icc 2 x.order,
            weakQuietCoefficientWeight x v u γ d) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (weak_quiet_coefficient_weight_weak_sum x v u)
      (by unfold WeakQuietExpansionCase.insertionPrice; have := plan.radius_pos x.R
          have := x.bounds.2.1; positivity)

/-- Extend a native operator by zero off its actual closed quiet margin. -/
def weakQuietSourceExtend {a b : ℝ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Set.Icc a b → E →L[ℝ] F) : ℝ → E →L[ℝ] F :=
  Function.extend Subtype.val L (fun _ => 0)

theorem weak_quiet_source_extend_apply {a b : ℝ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Set.Icc a b → E →L[ℝ] F) (t : Set.Icc a b) :
    weakQuietSourceExtend L t = L t :=
  Subtype.val_injective.extend_apply L (fun _ => 0) t

/-- Fixed test values of the zero extension retain genuine strong measurability. -/
theorem weak_quiet_source_extend_measurable {a b : ℝ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Set.Icc a b → E →L[ℝ] F) (hL : ∀ f, StronglyMeasurable (fun t => L t f)) (f : E) :
    StronglyMeasurable (fun t => weakQuietSourceExtend L t f) := by
  have he : (fun t => weakQuietSourceExtend L t f) =
      Function.extend Subtype.val (fun t => L t f) (fun _ => 0) := by
    funext t
    by_cases ht : t ∈ Set.Icc a b
    · have h1 := weak_quiet_source_extend_apply L ⟨t, ht⟩
      rw [h1, Subtype.val_injective.extend_apply (fun t => L t f) (fun _ => 0) ⟨t, ht⟩]
    · have hn : ¬∃ s : Set.Icc a b, s.val = t := by rintro ⟨s, rfl⟩; exact ht s.2
      rw [weakQuietSourceExtend, Function.extend_apply' L (fun _ => 0) t hn,
        Function.extend_apply' (fun t => L t f) (fun _ => 0) t hn, zero_apply]
  rw [he]
  exact (MeasurableEmbedding.subtype_coe measurableSet_Icc).stronglyMeasurable_extend
    (hL f) stronglyMeasurable_const

private theorem weakQuietOfOp_apply {T T' : (Vec 2 → ℝ) → Vec 2 → ℝ}
    {m R Kc : ℕ} {C : ℝ} (he : T = T') (A : TorusAdj T m R Kc C)
    (P : ℕ) (hP : P + m ≤ Kc) (φ : TorusHk (P + m) ℝ) :
    (A.ofOp he).adj P hP φ = A.adj P hP φ := by
  cases he
  rfl

private theorem weakQuietFiniteMeasurable {ι T E : Type*} [Fintype ι]
    [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ι → T → E) (hf : ∀ k, StronglyMeasurable (f k)) (σ : ℝ) :
    StronglyMeasurable (fun t => σ • ∑ k, f k t) := by
  have h := (Finset.univ.stronglyMeasurable_sum (fun k _ => hf k)).const_smul σ
  have he : (σ • ∑ k, f k) = (fun t => σ • ∑ k, f k t) := by
    funext t
    rw [Pi.smul_apply, Finset.sum_apply]
  exact he ▸ h

private theorem weakQuietAdjSum_apply {ι : Type*} [Fintype ι]
    {T : ι → (Vec 2 → ℝ) → Vec 2 → ℝ} {m R Kc : ℕ} {C : ι → ℝ}
    (A : ∀ k, TorusAdj (T k) m R Kc (C k)) (σ : ℝ)
    (Q : ℕ) (hQ : Q + m ≤ Kc) (φ : TorusHk (Q + m) ℝ) :
    ((TorusAdj.sum Finset.univ A).smul σ).adj Q hQ φ =
      σ • ∑ k, (A k).adj Q hQ φ := by
  let L : ι → TorusHk (Q + m) ℝ →L[ℝ] TorusHk Q ℝ := fun k => (A k).adj Q hQ
  change torusSmulCLM σ ((∑ k, L k) φ) = _
  rw [torusSmulCLM_apply]
  exact congrArg (fun z : TorusHk Q ℝ => σ • z) (_root_.sum_apply Finset.univ L φ)

private theorem weakQuietFinitePairing {ι : Type*} [Fintype ι]
    {P Q m : ℕ} (σ : ℝ)
    (L : ι → TorusHk (P + m) ℝ →L[ℝ] TorusHk P ℝ)
    (A : ι → TorusHk (Q + m) ℝ →L[ℝ] TorusHk Q ℝ)
    (f : TorusHk (P + m) ℝ) (φ : TorusHk (Q + m) ℝ)
    (h : ∀ k, inner ℝ (truncateTorusHk (Nat.zero_le P) (L k f))
      (truncateTorusHk (Nat.zero_le (Q + m)) φ) =
      inner ℝ (truncateTorusHk (Nat.zero_le (P + m)) f)
        (truncateTorusHk (Nat.zero_le Q) (A k φ))) :
    inner ℝ (truncateTorusHk (Nat.zero_le P) (σ • ∑ k, L k f))
      (truncateTorusHk (Nat.zero_le (Q + m)) φ) =
    inner ℝ (truncateTorusHk (Nat.zero_le (P + m)) f)
      (truncateTorusHk (Nat.zero_le Q) (σ • ∑ k, A k φ)) := by
  simp only [map_smul, map_sum, real_inner_smul_left, real_inner_smul_right,
    sum_inner, inner_sum]
  exact congrArg (fun z : ℝ => σ * z) (Finset.sum_congr rfl (fun k _ => h k))

/-- The actual signed insertion restricted to its native quiet margin. -/
structure WeakQuietInsertionOn (x : WeakQuietExpansionCase plan prices) where
  C : ∀ _v _u : x.Vertex, Set.Icc x.left x.right → ℝ
  adj : ∀ v u (t : Set.Icc x.left x.right),
    TorusAdj (x.source v u t) x.order (x.cap - x.order) x.cap (C v u t)
  adj_bound : ∀ v u t, (adj v u t).FBound x.radius
    (x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice * x.b v u)
  primal : ∀ (_v _u : x.Vertex) (P : ℕ), P + x.order ≤ x.cap →
    Set.Icc x.left x.right → TorusHk (P + x.order) ℝ →L[ℝ] TorusHk P ℝ
  primal_bound : ∀ v u P hP t f,
    Real.sqrt (factorialNormSq x.radius (primal v u P hP t f).val) ≤
      (x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice * x.b v u) *
        Real.sqrt (factorialNormSq x.radius f.val)
  paired : ∀ v u P Q hP hQ t (f : TorusHk (P + x.order) ℝ) (φ : TorusHk (Q + x.order) ℝ),
    inner ℝ (truncateTorusHk (Nat.zero_le P) (primal v u P hP t f))
      (truncateTorusHk (Nat.zero_le (Q + x.order)) φ) =
    inner ℝ (truncateTorusHk (Nat.zero_le (P + x.order)) f)
      (truncateTorusHk (Nat.zero_le Q) ((adj v u t).adj Q hQ φ))
  measurable : ∀ v u Q hQ (φ : TorusHk (Q + x.order) ℝ),
    StronglyMeasurable (fun t : Set.Icc x.left x.right => (adj v u t).adj Q hQ φ)

/-- Insertion data on the quiet margin extend by zero to the insertion interface. -/
def weakQuietInsertionOfOn (x : WeakQuietExpansionCase plan prices) (D : WeakQuietInsertionOn x) :
    WeakQuietInsertionData x where
  apply v u P hP := weakQuietSourceExtend (fun t => (D.adj v u t).adj P hP)
  adjoint v u t ht := ⟨D.C v u ⟨t, ht⟩, D.adj v u ⟨t, ht⟩,
    fun P hP => weak_quiet_source_extend_apply _ ⟨t, ht⟩, D.adj_bound v u ⟨t, ht⟩⟩
  measurable v u P hP φ := weak_quiet_source_extend_measurable _
    (D.measurable v u P hP) φ
  primal v u P hP := weakQuietSourceExtend (D.primal v u P hP)
  primal_bound v u P hP t ht f := by
    rw [weak_quiet_source_extend_apply _ ⟨t, ht⟩]
    exact D.primal_bound v u P hP ⟨t, ht⟩ f
  paired v u P Q hP hQ t ht f φ := by
    rw [weak_quiet_source_extend_apply _ ⟨t, ht⟩, weak_quiet_source_extend_apply _ ⟨t, ht⟩]
    exact D.paired v u P Q hP hQ ⟨t, ht⟩ f φ

section Aggregate
variable (hok : WeakQuietRowsPlanOK plan prices) (x : WeakQuietExpansionCase plan prices)
  (D : ∀ v u (k : WeakQuietSourceIndex x v u),
    WeakQuietSingleSourceData (weakQuietConstituentContext hok x v u k))

private def weakQuietAggregateC (v u : x.Vertex) (t : Set.Icc x.left x.right) : ℝ :=
  |Real.sqrt (x.mass u / x.mass v)| * ∑ k : WeakQuietSourceIndex x v u, (D v u k).C t

private def weakQuietAggregateParts (v u : x.Vertex) (t : Set.Icc x.left x.right)
    (k : WeakQuietSourceIndex x v u) :
    TorusAdj (weakQuietPrimalSource (k.2.1 - 1) ((x.c.stage x.i).physCoeff v u k.1 k.2.1 t))
      x.order (x.cap - x.order) x.cap ((D v u k).C t) :=
  (D v u k).adj t

private def weakQuietAggregateAdj (v u : x.Vertex) (t : Set.Icc x.left x.right) :
    TorusAdj (x.source v u t) x.order (x.cap - x.order) x.cap (weakQuietAggregateC hok x D v u t) :=
  ((TorusAdj.sum Finset.univ (weakQuietAggregateParts hok x D v u t)).smul
    (Real.sqrt (x.mass u / x.mass v))).ofOp (by
      funext ψ y
      exact weak_quiet_source_index_sum x v u t ψ y)

private def weakQuietAggregatePrimal (v u : x.Vertex) (P : ℕ) (hP : P + x.order ≤ x.cap)
    (t : Set.Icc x.left x.right) : TorusHk (P + x.order) ℝ →L[ℝ] TorusHk P ℝ :=
  Real.sqrt (x.mass u / x.mass v) •
    ∑ k : WeakQuietSourceIndex x v u, (D v u k).primal P hP t

private theorem weakQuietAggregateAdj_bound (v u : x.Vertex) (t : Set.Icc x.left x.right) : (weakQuietAggregateAdj hok x D v u t).FBound x.radius
    (x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice * x.b v u) := by
  unfold weakQuietAggregateAdj
  apply TorusAdj.FBound.ofOp
  apply TorusAdj.FBound.mono_const
    (TorusAdj.FBound.smul (Real.sqrt (x.mass u / x.mass v))
      (TorusAdj.FBound.sum Finset.univ (fun k => (D v u k).adj_bound t)))
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact weak_quiet_constituent_rates hok x v u

private theorem weakQuietAggregatePrimal_apply (v u : x.Vertex) (P : ℕ) (hP : P + x.order ≤ x.cap)
    (t : Set.Icc x.left x.right) (f : TorusHk (P + x.order) ℝ) :
    weakQuietAggregatePrimal hok x D v u P hP t f = Real.sqrt (x.mass u / x.mass v) •
      ∑ k : WeakQuietSourceIndex x v u, (D v u k).primal P hP t f := by
  dsimp only [weakQuietAggregatePrimal]
  rw [_root_.smul_apply]
  exact congrArg (fun z : TorusHk P ℝ => Real.sqrt (x.mass u / x.mass v) • z)
    (_root_.sum_apply _ _ _)

private theorem weakQuietAggregateAdj_transport (v u : x.Vertex) (Q : ℕ)
    (hQ : Q + x.order ≤ x.cap) (t : Set.Icc x.left x.right)
    (φ : TorusHk (Q + x.order) ℝ) :
    (weakQuietAggregateAdj hok x D v u t).adj Q hQ φ =
      ((TorusAdj.sum Finset.univ (weakQuietAggregateParts hok x D v u t)).smul
        (Real.sqrt (x.mass u / x.mass v))).adj Q hQ φ :=
  weakQuietOfOp_apply _ _ Q hQ φ

private theorem weakQuietAggregateAdj_apply (v u : x.Vertex) (Q : ℕ) (hQ : Q + x.order ≤ x.cap)
    (t : Set.Icc x.left x.right) (φ : TorusHk (Q + x.order) ℝ) :
    (weakQuietAggregateAdj hok x D v u t).adj Q hQ φ = Real.sqrt (x.mass u / x.mass v) •
      ∑ k : WeakQuietSourceIndex x v u, ((D v u k).adj t).adj Q hQ φ := by
  exact (weakQuietAggregateAdj_transport hok x D v u Q hQ t φ).trans
    (weakQuietAdjSum_apply (weakQuietAggregateParts hok x D v u t)
      (Real.sqrt (x.mass u / x.mass v)) Q hQ φ)

private theorem weakQuietAggregatePrimal_bound (v u : x.Vertex) (P : ℕ) (hP : P + x.order ≤ x.cap)
    (t : Set.Icc x.left x.right) (f : TorusHk (P + x.order) ℝ) :
    Real.sqrt (factorialNormSq x.radius (weakQuietAggregatePrimal hok x D v u P hP t f).val) ≤
    (x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice * x.b v u) *
      Real.sqrt (factorialNormSq x.radius f.val) := by
  rw [weakQuietAggregatePrimal_apply hok x D, sqrt_fNSq_torus_smul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (x.mass u / x.mass v) *
        ∑ k : WeakQuietSourceIndex x v u,
          (weakQuietConstituentContext hok x v u k).rate *
            Real.sqrt (factorialNormSq x.radius f.val) :=
      mul_le_mul_of_nonneg_left
        ((sqrt_fNSq_torus_sum_le x.radius Finset.univ _).trans
          (Finset.sum_le_sum (fun k _ => (D v u k).primal_bound P hP t f))) (Real.sqrt_nonneg _)
    _ = (Real.sqrt (x.mass u / x.mass v) *
        ∑ k : WeakQuietSourceIndex x v u, (weakQuietConstituentContext hok x v u k).rate) *
          Real.sqrt (factorialNormSq x.radius f.val) := by rw [← Finset.sum_mul, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (weak_quiet_constituent_rates hok x v u) (Real.sqrt_nonneg _)

private theorem weakQuietAggregate_paired (v u : x.Vertex) (P Q : ℕ) (hP : P + x.order ≤ x.cap) (hQ : Q + x.order ≤ x.cap)
    (t : Set.Icc x.left x.right) (f : TorusHk (P + x.order) ℝ) (φ : TorusHk (Q + x.order) ℝ) :
    inner ℝ (truncateTorusHk (Nat.zero_le P) (weakQuietAggregatePrimal hok x D v u P hP t f))
      (truncateTorusHk (Nat.zero_le (Q + x.order)) φ) =
    inner ℝ (truncateTorusHk (Nat.zero_le (P + x.order)) f)
      (truncateTorusHk (Nat.zero_le Q) ((weakQuietAggregateAdj hok x D v u t).adj Q hQ φ)) := by
  rw [weakQuietAggregatePrimal_apply hok x D, weakQuietAggregateAdj_apply hok x D]
  exact weakQuietFinitePairing (Real.sqrt (x.mass u / x.mass v))
    (fun k : WeakQuietSourceIndex x v u => (D v u k).primal P hP t)
    (fun k => ((D v u k).adj t).adj Q hQ) f φ
    (fun k => (D v u k).paired P Q hP hQ t f φ)

private theorem weakQuietAggregate_measurable (v u : x.Vertex) (Q : ℕ) (hQ : Q + x.order ≤ x.cap) (φ : TorusHk (Q + x.order) ℝ) :
    StronglyMeasurable (fun t : Set.Icc x.left x.right => (weakQuietAggregateAdj hok x D v u t).adj Q hQ φ) := by
  have he : (fun t : Set.Icc x.left x.right => (weakQuietAggregateAdj hok x D v u t).adj Q hQ φ) =
      (fun t : Set.Icc x.left x.right => Real.sqrt (x.mass u / x.mass v) •
        ∑ k : WeakQuietSourceIndex x v u, ((D v u k).adj t).adj Q hQ φ) := by
    funext t
    exact weakQuietAggregateAdj_apply hok x D v u Q hQ t φ
  rw [he]
  have hk (k : WeakQuietSourceIndex x v u) :
      StronglyMeasurable (fun t : Set.Icc x.left x.right => ((D v u k).adj t).adj Q hQ φ) :=
    (D v u k).measurable Q hQ φ
  exact weakQuietFiniteMeasurable
    (fun k : WeakQuietSourceIndex x v u => fun t : Set.Icc x.left x.right =>
      ((D v u k).adj t).adj Q hQ φ) hk (Real.sqrt (x.mass u / x.mass v))

include hok D in
/-- Finite aggregation spends only the literal b-entry budget. -/
theorem weak_quiet_aggregate_source : Nonempty (WeakQuietInsertionOn x) := by
  classical
  exact ⟨⟨weakQuietAggregateC hok x D, weakQuietAggregateAdj hok x D,
    weakQuietAggregateAdj_bound hok x D, weakQuietAggregatePrimal hok x D,
    weakQuietAggregatePrimal_bound hok x D, weakQuietAggregate_paired hok x D,
    weakQuietAggregate_measurable hok x D⟩⟩

end Aggregate

/-- **Source bound**, proved from the actual parent b budget and numerical reserve
conditions. All source identities, bounds, pairings and measurability are discharged. -/
theorem weak_quiet_source_insertions (hok : WeakQuietRowsPlanOK plan prices) :
    WeakQuietSourceInsertionStatement plan prices := by
  intro x
  let D (v u : x.Vertex) (k : WeakQuietSourceIndex x v u) :=
    Classical.choice (weak_quiet_single_source (weakQuietConstituentContext hok x v u k))
  obtain ⟨S⟩ := weak_quiet_aggregate_source hok x D
  exact ⟨weakQuietInsertionOfOn x S⟩

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleComparison.Coarse
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Finite Hilbert summation of the actual ordered quiet margin paths. Equality of
value pairings identifies the terminal Sobolev field; factorial norms then
sum against exactly the b-matrix kernel, including its empty path. -/

variable {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}

/-- The finite weighted walk sum is exactly the corrected quiet margin kernel. -/
theorem weak_quiet_walk_kernel_sum (prices : WeakQuietPathPrices)
    {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → ι → ℝ) (v u : ι) (z : ℝ) :
    (∑ n : Fin (prices.depth R + 1), ∑ π : WeakQuietWalk ι n.val v u,
      prices.scalar R n.val * weakQuietWalkWeight b n.val v u π * z) =
      weakQuietMarginPathKernel prices R b v u * z := by
  have hn (n : Fin (prices.depth R + 1)) :
      (∑ π : WeakQuietWalk ι n.val v u,
        prices.scalar R n.val * weakQuietWalkWeight b n.val v u π * z) =
      (prices.scalar R n.val * (Matrix.of b ^ n.val) v u) * z := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, weak_quiet_walk_weight_sum]
  simp_rw [hn]
  rw [← Finset.sum_mul]
  congr 1
  rw [Fin.sum_univ_eq_sum_range
    (fun n : ℕ => prices.scalar R n * (Matrix.of b ^ n) v u) (prices.depth R + 1),
    Finset.sum_range_succ' (fun n : ℕ => prices.scalar R n * (Matrix.of b ^ n) v u)
      (prices.depth R)]
  unfold weakQuietMarginPathKernel
  rw [pow_zero, Matrix.one_apply]
  by_cases hv : v = u
  · simp only [ite_eq_left hv, mul_one]
    exact add_comm _ _
  · simp only [ite_eq_right hv, mul_zero, add_zero, zero_add]

/-- Mass conjugation gives exactly the factorial norm of the native row. -/
theorem weak_quiet_value_size (x : WeakQuietExpansionCase plan prices) (v : x.Vertex) (t : ℝ) :
    Real.sqrt (factorialNormSq x.radius (x.value v t).val) =
      Real.sqrt ((x.mass v)⁻¹ * factorialNormSq x.radius (x.run.Ur x.i v t).val) := by
  dsimp only [WeakQuietExpansionCase.value]
  rw [sqrt_fNSq_torus_smul, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sqrt_mul (inv_nonneg.mpr (x.mass_pos v).le)]

/-- **Sum**: the exact terminal field is the finite sum of represented
paths, and the triangle inequality gives its actual b-kernel estimate. -/
theorem weak_quiet_path_summation : WeakQuietPathSummationStatement plan prices := by
  classical
  intro x S H hpaths hrep v
  let Z (u : x.Vertex) (n : Fin (prices.depth x.R + 1))
      (π : WeakQuietWalk x.Vertex n.val v u) : TorusHk x.R.Kw ℝ :=
    (hrep n.val (Nat.le_of_lt_succ n.isLt) v u π).choose
  let total : TorusHk x.R.Kw ℝ :=
    ∑ u, ∑ n : Fin (prices.depth x.R + 1), ∑ π : WeakQuietWalk x.Vertex n.val v u, Z u n π
  have hpair (φ : TorusHk x.cap ℝ) :
      inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value v x.right))
        (truncateTorusHk (Nat.zero_le x.cap) φ) =
      inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) total)
        (truncateTorusHk (Nat.zero_le x.cap) φ) := by
    rw [hpaths v φ]
    dsimp only [total]
    simp only [map_sum, sum_inner]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro π _
    exact ((hrep n.val (Nat.le_of_lt_succ n.isLt) v u π).choose_spec.1 φ).symm
  have hzero : truncateTorusHk (Nat.zero_le x.R.Kw) (x.value v x.right) =
      truncateTorusHk (Nat.zero_le x.R.Kw) total := by
    have hh := (CycleJointProofs.truncateTorusHk_denseRange (E := ℝ) (Nat.zero_le x.cap)).equalizer
      (continuous_const.inner continuous_id : Continuous (fun φ : TorusHk 0 ℝ =>
        inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value v x.right)) φ))
      (continuous_const.inner continuous_id : Continuous (fun φ : TorusHk 0 ℝ =>
        inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) total) φ)) (funext hpair)
    exact ext_inner_right ℝ (congrFun hh)
  have he : x.value v x.right = total :=
    TorusHk.ext_value (congrArg (fun z : TorusHk 0 ℝ => torusHkValueCLM z) hzero)
  rw [← weak_quiet_value_size, he]
  calc
    _ ≤ ∑ u, ∑ n : Fin (prices.depth x.R + 1), ∑ π : WeakQuietWalk x.Vertex n.val v u,
        Real.sqrt (factorialNormSq x.radius (Z u n π).val) := by
      apply (sqrt_fNSq_torus_sum_le x.radius Finset.univ _).trans
      apply Finset.sum_le_sum
      intro u _
      apply (sqrt_fNSq_torus_sum_le x.radius Finset.univ _).trans
      apply Finset.sum_le_sum
      intro n _
      exact sqrt_fNSq_torus_sum_le x.radius Finset.univ _
    _ ≤ ∑ u, ∑ n : Fin (prices.depth x.R + 1), ∑ π : WeakQuietWalk x.Vertex n.val v u,
        prices.scalar x.R n.val * weakQuietWalkWeight x.b n.val v u π * x.inputSize u := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro n _
      exact Finset.sum_le_sum (fun π _ => (hrep n.val (Nat.le_of_lt_succ n.isLt) v u π).choose_spec.2)
    _ = _ := Finset.sum_congr rfl (fun u _ => weak_quiet_walk_kernel_sum prices x.R x.b v u (x.inputSize u))

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Final pre-data prices for the smoothing layer. Scalar prices are chosen after the finite
reserve, and the trace constant is then their finite b-kernel polynomial.
Neither the ambient order cap nor the construction nor the datum is used. -/

/-- The smoothing layer on any common plan satisfying the explicit numerical depth, reserve,
radius, scalar-price and trace-price conditions. No analytic leaf remains. -/
theorem weak_quiet_smoothing_of_plan_conditions {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (hok : WeakQuietRowsPlanOK plan prices)
    (hcoeff : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      0 ≤ plan.coeffC R)
    (hscalar : WeakQuietScalarPricesOK plan prices)
    (htrace : WeakQuietMarginPriceStatement plan prices) :
    WeakQuietSmoothingStatement plan := by
  have hex : WeakQuietMarginExpansionStatement plan prices :=
    @weak_quiet_margin_expansion_of_subingredients plan prices
      (weak_quiet_source_insertions hok) (weak_quiet_ordered_paths hok)
      (weak_quiet_scalar_paths hok hscalar) weak_quiet_path_summation
  exact @weak_quiet_smoothing_of_quiet_margin_estimates plan prices hcoeff hex htrace

end AVRegularity.WeakEntryProofs.Assembly
end
end
end
