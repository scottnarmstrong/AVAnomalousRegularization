-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeakAssembly.PairedForcingCostSchur
public import AVRegularity.EntryWeakAssembly.Assembly.KernelPriceTransport
public import AVRegularity.EntryWeakAssembly.CoordinateWordFiniteWindowHigherProduction

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Assembly

/-! The quiet margin bounds keep the actual aggregated coefficient matrix.
The stored-record kernel remains available for comparison energy only. -/

/-- The parent quiet margin bounds with the coefficient matrix `b` explicit. -/
def WeakParentQuietMarginBoundsWith {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (b : CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ) : Prop :=
  0 < c.D.eps (i - 1) ∧ 0 < c.D.κ c.M ∧
  r.tq (i + 1) ≤ r.tq i - c.D.eps (i - 1) ^ 2 / c.D.κ c.M ∧
  r.tq i - ocTauP c.D.α c.D.q c.D.Λ i / 2 ≤ r.tq i - c.D.eps (i - 1) ^ 2 / c.D.κ c.M ∧
  (∀ v u, 0 ≤ b v u) ∧ (∀ v, ∑ u, b v u ≤ plan.coeffC R) ∧
  (∀ u, ∑ v, b v u ≤ plan.coeffC R) ∧
  (∀ v u (γ : (c.stage i).fam.Γ v u) d, 2 ≤ d → d ≤ c.Dm →
    ∀ t ∈ Set.Icc (r.tq i - c.D.eps (i - 1) ^ 2 / c.D.κ c.M) (r.tq i),
      ContDiff ℝ (plan.jetOrder R) ((c.stage i).physCoeff v u γ d t)) ∧
  ∀ v u,
    ENNReal.ofReal (Real.sqrt (weakMass c.D A.Nw A.Jw A.η₀ u.1 /
      weakMass c.D A.Nw A.Jw A.η₀ v.1)) *
    ∑ γ : (c.stage i).fam.Γ v u, ∑ d ∈ Finset.Icc 2 c.Dm,
      coefficientSeminorm (c.D.eps (i - 1)) (plan.jetOrder R)
        (r.tq i - c.D.eps (i - 1) ^ 2 / c.D.κ c.M) (r.tq i)
        ((c.stage i).physCoeff v u γ d) *
        (ENNReal.ofReal (c.D.κ c.M * c.D.eps (i - 1) ^ (d - 2)))⁻¹ ≤ ENNReal.ofReal (b v u)

theorem weakParentQuietMarginBounds_iff {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (i : ℕ) : WeakParentQuietMarginBounds c r i ↔ ∃ b, WeakParentQuietMarginBoundsWith c r i b := by
  constructor
  · rintro ⟨he, hk, hleft, hmid, b, hb⟩
    exact ⟨b, he, hk, hleft, hmid, hb⟩
  · rintro ⟨b, he, hk, hleft, hmid, hb⟩
    exact ⟨he, hk, hleft, hmid, b, hb⟩

/-- The positive path kernel of a matrix `b`: the empty path on the diagonal and the `b`-paths
with `n + 1 ≤ depth` steps. -/
def weakQuietMarginPathKernel (prices : WeakQuietPathPrices) {B} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → ι → ℝ)
    (v u : ι) : ℝ :=
  (if v = u then prices.scalar R 0 else 0) +
    ∑ n ∈ Finset.range (prices.depth R), prices.scalar R (n + 1) * (Matrix.of b ^ (n + 1)) v u

/-- The source path depth and native finite jet reserve. These choices depend
only on the request and are fixed before the construction cap `Dm`. -/
def WeakQuietMarginDepthOK (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) : Prop :=
  ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    A.Jw * A.Rw + 1 ≤ prices.depth R ∧
      R.Kw + prices.depth R * (1 + A.Jw * A.Nw) ≤ plan.jetOrder R

/-- **The smoothing layer, restated.** The final rows are dominated by the `b`-path kernel of any quiet margin matrix. -/
def WeakQuietMarginExpansionStatement (plan : WeakPassagePlan)
    (prices : WeakQuietPathPrices) : Prop :=
  ∀ {B} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → WeakQuietWindow c r i →
    ∀ b, WeakParentQuietMarginBoundsWith c r i b →
    ∀ v : CompIn (c.stage i).comps,
      Real.sqrt ((weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
        factorialNormSq (plan.radius R * c.D.eps (i - 1)) (r.Ur i v (r.tq i)).val) ≤
      ∑ u, weakQuietMarginPathKernel prices R b v u *
        Real.sqrt ((weakMass c.D A.Nw A.Jw A.η₀ u.1)⁻¹ *
          factorialNormSq 1 (truncateTorusHk (Nat.zero_le R.Kw)
            (r.Ur i u (r.tq i - c.D.eps (i - 1) ^ 2 / c.D.κ c.M))).val)

/-- The price: pure plan arithmetic, with no stage. -/
def WeakQuietMarginPriceStatement (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) : Prop :=
  ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    prices.scalar R 0 + ∑ n ∈ Finset.range (prices.depth R),
      prices.scalar R (n + 1) * plan.coeffC R ^ (n + 1) ≤ plan.traceC R

/-- The purely finite matrix calculation behind the quiet margin kernel. -/
def WeakQuietMarginSchurStatement : Prop :=
  ∀ (prices : WeakQuietPathPrices) {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : ι → ι → ℝ) (C : ℝ), 0 ≤ C → (∀ v u, 0 ≤ b v u) →
    (∀ v, ∑ u, b v u ≤ C) → (∀ u, ∑ v, b v u ≤ C) →
    (∀ v u, 0 ≤ weakQuietMarginPathKernel prices R b v u) ∧
    (∀ v, ∑ u, weakQuietMarginPathKernel prices R b v u ≤
      prices.scalar R 0 + ∑ n ∈ Finset.range (prices.depth R),
        prices.scalar R (n + 1) * C ^ (n + 1)) ∧
    (∀ u, ∑ v, weakQuietMarginPathKernel prices R b v u ≤
      prices.scalar R 0 + ∑ n ∈ Finset.range (prices.depth R),
        prices.scalar R (n + 1) * C ^ (n + 1))

/-- Exact quiet smoothing from the corrected quiet margin-matrix expansion, its numeric
price, and finite matrix algebra. No statement about untrimmed quiet times occurs. -/
theorem weak_quiet_smoothing_of_quiet_margin_ingredients (plan : WeakPassagePlan)
    (prices : WeakQuietPathPrices)
    (hcoeff : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A), 0 ≤ plan.coeffC R)
    (hexpand : WeakQuietMarginExpansionStatement plan prices)
    (hprice : WeakQuietMarginPriceStatement plan prices)
    (hschur : WeakQuietMarginSchurStatement) : WeakQuietSmoothingStatement plan := by
  classical
  intro B A R c r i hi hit hw hc bound hb
  obtain ⟨b, hbc⟩ := (weakParentQuietMarginBounds_iff c r i).mp hc
  have hbc_keep := hbc
  obtain ⟨_, hk, hleft, _, hnonneg, hrow, hcol, _⟩ := hbc
  let t := r.tq i - c.D.eps (i - 1) ^ 2 / c.D.κ c.M
  let π := fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1
  let x := fun v => Real.sqrt ((π v)⁻¹ * factorialNormSq 1
    (truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t)).val)
  let y := fun v => Real.sqrt ((π v)⁻¹ *
    factorialNormSq (plan.radius R * c.D.eps (i - 1)) (r.Ur i v (r.tq i)).val)
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge B).trans c.base_ge)
  have hπ : ∀ v, 0 < π v := fun v => weakMass_pos c.D _ _ _ A.Nw_pos A.Jw_pos
    (fun _ => Construction.Stream.ocEpsilon_pos hΛ) v.1
  obtain ⟨hK, hr, hcol⟩ := hschur prices R b (plan.coeffC R) (hcoeff R) hnonneg hrow hcol
  have hcost : 0 ≤ prices.scalar R 0 + ∑ n ∈ Finset.range (prices.depth R),
      prices.scalar R (n + 1) * plan.coeffC R ^ (n + 1) :=
    add_nonneg (prices.nonneg R 0) (Finset.sum_nonneg fun n _ =>
      mul_nonneg (prices.nonneg R _) (pow_nonneg (hcoeff R) _))
  have hs := quiet_finite_schur (weakQuietMarginPathKernel prices R b) x y (plan.traceC R)
    (hcost.trans (hprice R)) hK (fun _ => Real.sqrt_nonneg _)
    (hexpand c r i hi hit hw b hbc_keep)
    (fun v => (hr v).trans (hprice R)) (fun u => (hcol u).trans (hprice R))
  have hx : ∀ v, x v ^ 2 = (π v)⁻¹ * factorialNormSq 1
      (truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t)).val := fun v =>
    Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr (hπ v).le) (factorialNormSq_nonneg _ _))
  have hy : ∀ v, y v ^ 2 = (π v)⁻¹ *
      factorialNormSq (plan.radius R * c.D.eps (i - 1)) (r.Ur i v (r.tq i)).val := fun v =>
    Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr (hπ v).le) (factorialNormSq_nonneg _ _))
  simp only [hx, hy] at hs
  have hnorm : weightedNorm (plan.radius R * c.D.eps (i - 1)) π (fun _ => 1)
      (fun v => r.Ur i v (r.tq i)) ≤ plan.traceC R *
      weightedNorm 1 π (fun _ => 1) (fun v => truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t)) := by
    simpa only [weightedNorm, massNormSq, one_pow, div_one] using hs
  have ht : t ∈ Set.Icc (r.tq (i + 1)) (r.tq i) :=
    ⟨hleft, sub_le_self _ (div_nonneg (sq_nonneg _) hk.le)⟩
  exact hnorm.trans (mul_le_mul_of_nonneg_left (hb t ht) (hcost.trans (hprice R)))

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Coarse
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Smoothing layer sub-assembly. Walks use the actual coefficient matrix, including its
empty path. The analytic paths are iterated time-ordered adjoint insertions,
not stored-record products. All orders and scalar prices precede `Dm`. -/

/-- A reversed vertex walk: its first insertion is the latest source. Empty
walks exist exactly when the two endpoints agree. -/
def WeakQuietWalk (ι : Type) : ℕ → ι → ι → Type
  | 0, v, u => PLift (v = u)
  | n + 1, _, u => Σ w : ι, WeakQuietWalk ι n w u

instance weakQuietWalkFinite {ι : Type} [Finite ι] (n : ℕ) (v u : ι) :
    Finite (WeakQuietWalk ι n v u) := by
  induction n generalizing v with
  | zero => change Finite (PLift (v = u)); infer_instance
  | succ n ih =>
    change Finite (Σ w : ι, WeakQuietWalk ι n w u)
    let (w : ι) : Finite (WeakQuietWalk ι n w u) := ih w
    infer_instance

instance weakQuietWalkFintype {ι : Type} [Fintype ι] (n : ℕ) (v u : ι) :
    Fintype (WeakQuietWalk ι n v u) := Fintype.ofFinite _

/-- A walk carries the product of its actual quiet margin-matrix entries. -/
def weakQuietWalkWeight {ι : Type} (b : ι → ι → ℝ) :
    (n : ℕ) → (v u : ι) → WeakQuietWalk ι n v u → ℝ
  | 0, _, _, _ => 1
  | n + 1, v, u, π => b v π.1 * weakQuietWalkWeight b n π.1 u π.2

/-- One actual heat quiet margin, with all source premises retained. -/
structure WeakQuietExpansionCase (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) where
  B : WeakCoefficientBase
  A : WeakCoefficientPhysical B
  R : WeakPassageRequest A
  c : WeakPassageInstance plan R
  run : WeakPassageRun c
  i : ℕ
  level_lt : c.M < i
  level_le : i ≤ c.M + A.Jw
  quiet : WeakQuietWindow c run i
  b : CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ
  bounds : WeakParentQuietMarginBoundsWith c run i b

namespace WeakQuietExpansionCase
variable {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}

abbrev Vertex (x : WeakQuietExpansionCase plan prices) := CompIn (x.c.stage x.i).comps

def left (x : WeakQuietExpansionCase plan prices) : ℝ :=
  x.run.tq x.i - x.c.D.eps (x.i - 1) ^ 2 / x.c.D.κ x.c.M

def right (x : WeakQuietExpansionCase plan prices) : ℝ := x.run.tq x.i

def radius (x : WeakQuietExpansionCase plan prices) : ℝ :=
  plan.radius x.R * x.c.D.eps (x.i - 1)

/-- The maximal weak differential order; it does not use the ambient cap. -/
def order (x : WeakQuietExpansionCase plan prices) : ℕ := 1 + x.A.Jw * x.A.Nw

/-- The finite adjoint test reserve. -/
def cap (x : WeakQuietExpansionCase plan prices) : ℕ :=
  x.R.Kw + prices.depth x.R * x.order

def mass (x : WeakQuietExpansionCase plan prices) (v : x.Vertex) : ℝ :=
  weakMass x.c.D x.A.Nw x.A.Jw x.A.η₀ v.1

/-- Conjugating by the prescribed masses makes each source budget equal to b. -/
def value (x : WeakQuietExpansionCase plan prices) (v : x.Vertex) (t : ℝ) :
    TorusHk x.R.Kw ℝ := Real.sqrt (x.mass v)⁻¹ • x.run.Ur x.i v t

def inputSize (x : WeakQuietExpansionCase plan prices) (u : x.Vertex) : ℝ :=
  Real.sqrt ((x.mass u)⁻¹ * factorialNormSq 1
    (truncateTorusHk (Nat.zero_le x.R.Kw) (x.run.Ur x.i u x.left)).val)

/-- The actual complete incoming differential source, after mass conjugation.
Every identity and every physical order is kept; the finite-order lemma must
prove the terms above `order` vanish. -/
def source (x : WeakQuietExpansionCase plan prices) (v u : x.Vertex) (t : ℝ)
    (ψ : Vec 2 → ℝ) : Vec 2 → ℝ :=
  fun y => Real.sqrt (x.mass u / x.mass v) *
    ∑ γ : (x.c.stage x.i).fam.Γ v u, ∑ d ∈ Finset.Icc 2 x.c.Dm,
      weakQuietPrimalSource (d - 1) ((x.c.stage x.i).physCoeff v u γ d t) ψ y

/-- A dimensionless upper price for one insertion at every finite reserve. -/
def insertionPrice (x : WeakQuietExpansionCase plan prices) : ℝ :=
  (2 * (x.cap + 1 : ℕ) / plan.radius x.R) ^ x.order

/-- Monotonicity of the fixed finite path reserve. -/
theorem path_reserve (x : WeakQuietExpansionCase plan prices) (n : ℕ)
    (hn : n ≤ prices.depth x.R) : n * x.order ≤ x.cap :=
  (Nat.mul_le_mul_right x.order hn).trans (Nat.le_add_left _ _)

end WeakQuietExpansionCase

/-- Actual source adjoints at the finite weak reserve. The witnesses identify
the operator with the physical differential source, rather than merely
postulating its norm. Off the quiet margin the maps are its zero extension. -/
structure WeakQuietInsertionData {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}
    (x : WeakQuietExpansionCase plan prices) where
  apply : ∀ (_v _u : x.Vertex) (P : ℕ), P + x.order ≤ x.cap →
    ℝ → TorusHk (P + x.order) ℝ →L[ℝ] TorusHk P ℝ
  adjoint : ∀ v u t, t ∈ Set.Icc x.left x.right →
    ∃ C : ℝ, ∃ Adj : TorusAdj (x.source v u t) x.order (x.cap - x.order) x.cap C,
      (∀ P (hP : P + x.order ≤ x.cap), apply v u P hP t = Adj.adj P hP) ∧
      Adj.FBound x.radius
        (x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice * x.b v u)
  measurable : ∀ v u P hP (φ : TorusHk (P + x.order) ℝ),
    StronglyMeasurable (fun t => apply v u P hP t φ)
  /-- The same physical source on positive reserves, used after the long gap. -/
  primal : ∀ (_v _u : x.Vertex) (P : ℕ), P + x.order ≤ x.cap →
    ℝ → TorusHk (P + x.order) ℝ →L[ℝ] TorusHk P ℝ
  primal_bound : ∀ v u P hP t, t ∈ Set.Icc x.left x.right →
    ∀ f : TorusHk (P + x.order) ℝ,
      Real.sqrt (factorialNormSq x.radius (primal v u P hP t f).val) ≤
        (x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice * x.b v u) *
          Real.sqrt (factorialNormSq x.radius f.val)
  /-- Primal and adjoint are two native realizations of the same source. -/
  paired : ∀ v u P Q hP hQ t, t ∈ Set.Icc x.left x.right →
    ∀ (f : TorusHk (P + x.order) ℝ) (φ : TorusHk (Q + x.order) ℝ),
      inner ℝ (truncateTorusHk (Nat.zero_le P) (primal v u P hP t f))
        (truncateTorusHk (Nat.zero_le (Q + x.order)) φ) =
      inner ℝ (truncateTorusHk (Nat.zero_le (P + x.order)) f)
        (truncateTorusHk (Nat.zero_le Q) (apply v u Q hQ t φ))

/-- The genuine backward scalar propagator on the parent velocity. The entire
closed quiet margin is used, and every subwindow carries the native weak equation. -/
structure WeakQuietBackwardEvolution {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}
    (x : WeakQuietExpansionCase plan prices) where
  apply : ∀ P : ℕ, ℝ → ℝ → TorusHk P ℝ → TorusHk P ℝ
  native : ∀ P, P ≤ x.cap → ∀ a b, x.left ≤ a → a ≤ b → b ≤ x.right →
    ∀ φ : TorusHk P ℝ, ∃ z : ℝ → TorusHk P ℝ, ∃ zw : ℝ → TorusHk (P + 1) ℝ,
      WeakScalarTorusSolution (x.c.D.κ x.c.M) (-b) (-a)
        (fun t y => -streamVel (x.c.D.Φ (x.i - 1)) (-t) y) P φ z zw ∧
      apply P a b φ = z (-a)

/-- A time-ordered adjoint source path. The integral is an actual Bochner
integral in H0. Its existence is part of the scalar path statement, not a
convention that a nonintegrable integral should stand for the evolution. -/
def weakQuietWalkDual {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}
    (x : WeakQuietExpansionCase plan prices) (S : WeakQuietInsertionData x)
    (H : WeakQuietBackwardEvolution x) :
    (n : ℕ) → n ≤ prices.depth x.R → (v u : x.Vertex) → WeakQuietWalk x.Vertex n v u →
    ℝ → ℝ → TorusHk (n * x.order) ℝ → TorusHk 0 ℝ
  | 0, _, _, _, _, a, b, φ => H.apply 0 a b (truncateTorusHk (by simp) φ)
  | n + 1, hn, v, u, π, a, b, φ =>
    ∫ t in a..b, weakQuietWalkDual x S H n (by omega) π.1 u π.2 a t
      (S.apply v π.1 (n * x.order)
        (by simpa only [Nat.succ_mul] using x.path_reserve (n + 1) hn) t
        (truncateTorusHk (by rw [Nat.succ_mul]) (H.apply ((n + 1) * x.order) t b φ)))

/-- Every actual iterated source integrand is integrable on its subwindow.
This is the analytic premise needed when commuting finite sums and integrals. -/
def WeakQuietWalkIntegrable {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}
    (x : WeakQuietExpansionCase plan prices) (S : WeakQuietInsertionData x)
    (H : WeakQuietBackwardEvolution x) : Prop :=
  ∀ n (hn : n + 1 ≤ prices.depth x.R) (v u : x.Vertex)
        (π : WeakQuietWalk x.Vertex (n + 1) v u) a b,
        x.left ≤ a → a ≤ b → b ≤ x.right →
        ∀ φ : TorusHk ((n + 1) * x.order) ℝ,
          IntegrableOn (fun t => weakQuietWalkDual x S H n (by omega) π.1 u π.2 a t
            (S.apply v π.1 (n * x.order)
              (by simpa only [Nat.succ_mul] using x.path_reserve (n + 1) hn) t
              (truncateTorusHk (by rw [Nat.succ_mul]) (H.apply ((n + 1) * x.order) t b φ)))) (Set.Icc a b)

/-- A represented path functional, together with its positive-order terminal
cost. The test reserve is finite and fixed before Dm. -/
def WeakQuietPathRepresented {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}
    (x : WeakQuietExpansionCase plan prices) (S : WeakQuietInsertionData x)
    (H : WeakQuietBackwardEvolution x) (n : ℕ) (hn : n ≤ prices.depth x.R)
    (v u : x.Vertex) (π : WeakQuietWalk x.Vertex n v u)
    (Z : TorusHk x.R.Kw ℝ) : Prop :=
  (∀ φ : TorusHk x.cap ℝ,
    inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) Z)
      (truncateTorusHk (Nat.zero_le x.cap) φ) =
    inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value u x.left))
      (weakQuietWalkDual x S H n hn v u π x.left x.right
        (truncateTorusHk (x.path_reserve n hn) φ))) ∧
  Real.sqrt (factorialNormSq x.radius Z.val) ≤
    prices.scalar x.R n * weakQuietWalkWeight x.b n v u π * x.inputSize u

/-- **Source bound**: the signed Sobolev bound of an actual aggregate source,
with its given b-entry. Positive source flux bounds are already proved in
QuietSourceFluxBounds; the remaining native adjoint identification is explicit. -/
def WeakQuietSourceInsertionStatement (plan : WeakPassagePlan)
    (prices : WeakQuietPathPrices) : Prop :=
  ∀ x : WeakQuietExpansionCase plan prices, Nonempty (WeakQuietInsertionData x)

/-- **Path expansion**: the exact transposed, finite Duhamel expansion. Nilpotence of
the actual weak family removes the remainder at the depth fixed by the plan. -/
def WeakQuietOrderedPathsStatement (plan : WeakPassagePlan)
    (prices : WeakQuietPathPrices) : Prop :=
  ∀ (x : WeakQuietExpansionCase plan prices) (S : WeakQuietInsertionData x)
    (H : WeakQuietBackwardEvolution x), WeakQuietWalkIntegrable x S H →
    ∀ (v : x.Vertex) (φ : TorusHk x.cap ℝ),
    inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value v x.right))
      (truncateTorusHk (Nat.zero_le x.cap) φ) =
    ∑ u, ∑ n : Fin (prices.depth x.R + 1),
      ∑ π : WeakQuietWalk x.Vertex n.val v u,
        inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value u x.left))
          (weakQuietWalkDual x S H n.val (Nat.le_of_lt_succ n.isLt)
            v u π x.left x.right
            (truncateTorusHk (x.path_reserve n.val (Nat.le_of_lt_succ n.isLt)) φ))

/-- **One step**: one scalar interval between successive insertions. Its proof
uses positive propagation before the longest interval, negative propagation
after it, and negative-to-positive smoothing on that interval. No width-positive
regularizer is used on this width-zero quiet margin. -/
def WeakQuietScalarPathStatement (plan : WeakPassagePlan)
    (prices : WeakQuietPathPrices) : Prop :=
  ∀ (x : WeakQuietExpansionCase plan prices) (S : WeakQuietInsertionData x),
    ∃ H : WeakQuietBackwardEvolution x,
      WeakQuietWalkIntegrable x S H ∧
      ∀ n (hn : n ≤ prices.depth x.R) v u (π : WeakQuietWalk x.Vertex n v u),
        ∃ Z : TorusHk x.R.Kw ℝ, WeakQuietPathRepresented x S H n hn v u π Z

/-- **Sum**: identify a terminal Sobolev field from the represented paths,
then sum their norms. This is finite Hilbert algebra and the b-walk identity. -/
def WeakQuietPathSummationStatement (plan : WeakPassagePlan)
    (prices : WeakQuietPathPrices) : Prop :=
  ∀ (x : WeakQuietExpansionCase plan prices) (S : WeakQuietInsertionData x)
    (H : WeakQuietBackwardEvolution x),
    (∀ v (φ : TorusHk x.cap ℝ),
      inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value v x.right))
        (truncateTorusHk (Nat.zero_le x.cap) φ) =
      ∑ u, ∑ n : Fin (prices.depth x.R + 1),
        ∑ π : WeakQuietWalk x.Vertex n.val v u,
          inner ℝ (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value u x.left))
            (weakQuietWalkDual x S H n.val (Nat.le_of_lt_succ n.isLt)
              v u π x.left x.right
              (truncateTorusHk (x.path_reserve n.val (Nat.le_of_lt_succ n.isLt)) φ))) →
    (∀ n (hn : n ≤ prices.depth x.R) v u (π : WeakQuietWalk x.Vertex n v u),
      ∃ Z : TorusHk x.R.Kw ℝ, WeakQuietPathRepresented x S H n hn v u π Z) →
    ∀ v, Real.sqrt ((x.mass v)⁻¹ * factorialNormSq x.radius (x.run.Ur x.i v x.right).val) ≤
      ∑ u, weakQuietMarginPathKernel prices x.R x.b v u * x.inputSize u

/-- The exact smoothing expansion from its four analytic/algebraic groups. -/
theorem weak_quiet_margin_expansion_of_subingredients (plan : WeakPassagePlan)
    (prices : WeakQuietPathPrices)
    (hsource : WeakQuietSourceInsertionStatement plan prices)
    (hpaths : WeakQuietOrderedPathsStatement plan prices)
    (hstep : WeakQuietScalarPathStatement plan prices)
    (hsum : WeakQuietPathSummationStatement plan prices) :
    WeakQuietMarginExpansionStatement plan prices := by
  intro B A R c r i hi hit hw b hb v
  let x : WeakQuietExpansionCase plan prices := ⟨B, A, R, c, r, i, hi, hit, hw, b, hb⟩
  obtain ⟨S⟩ := hsource x
  obtain ⟨H, hI, hrepresented⟩ := hstep x S
  exact hsum x S H (hpaths x S H hI) hrepresented v

end AVRegularity.WeakEntryProofs.Assembly
end
