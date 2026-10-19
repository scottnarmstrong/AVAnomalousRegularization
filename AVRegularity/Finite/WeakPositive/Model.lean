-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
public import AVRegularity.Construction.Preservation.FullLift.CovarianceTimeMeasurable
public import AVRegularity.EntryWeak.FluxProductionArithmetic
import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
open scoped Classical ENNReal
namespace AVRegularity.Finite.WeakLift

/-! Summing original record jets at a fixed menu cap, independent of the ambient degree. -/

open Construction.Preservation.FullLift

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

omit [Fintype ι] in
private theorem weak_liftedFiber_fixed_cap_price (F : ChartedFamily ι h D P Ctx)
    (cap : ℕ) (hcap : ∀ v u (δ : F.Γ v u), (F.identity v u δ).maxOrder ≤ cap)
    (p : P) (ctx : Ctx p) (v u : ι) (d : Finset.Icc 2 D)
    (S : Set ℝ) (clock lam A : ℝ) (hA : 0 ≤ A) (r q : ℕ)
    (hjet : ∀ δ : F.Γ v u, d.1 ≤ (F.identity v u δ).maxOrder → ∀ I,
      jetSup S r q (fun t X z => F.flux p ctx v u δ d.1 I (clock * t) (lam • X) z) ≤
        ENNReal.ofReal (A * (F.identity v u δ).record.size)) :
    (((liftEdges clock lam (F.fiber p ctx)) v u d).map fun γ =>
      ENNReal.ofReal ‖γ.map‖ * ∑ I, jetSup S r q (γ.coeff I)).sum ≤
        ENNReal.ofReal (2 ^ cap * A * ∑ δ, ‖(F.identity v u δ).map‖ *
          (F.identity v u δ).record.size) := by
  let price (δ : F.Γ v u) := ENNReal.ofReal
    (2 ^ cap * A * (‖(F.identity v u δ).map‖ * (F.identity v u δ).record.size))
  have hs : ((Finset.univ.toList : List (F.Γ v u)).map price).sum =
      ENNReal.ofReal (2 ^ cap * A * ∑ δ, ‖(F.identity v u δ).map‖ *
        (F.identity v u δ).record.size) := by
    rw [Finset.sum_map_toList]
    dsimp only [price]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun δ _ =>
      mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hA)
        (mul_nonneg (norm_nonneg _) (F.identity v u δ).record.size_nonneg)), ← Finset.mul_sum]
  apply le_trans _ (le_of_eq hs)
  unfold liftEdges ChartedFamily.fiber
  rw [List.map_map]
  apply filteredList_positive_sum_le
  intro δ γ hγ
  split_ifs at hγ with hd
  · cases hγ
    dsimp only [Function.comp_def, price]
    calc
      _ ≤ ENNReal.ofReal ‖(F.identity v u δ).map‖ *
          ∑ _I : DerivativeWord2 (d.1 - 1), ENNReal.ofReal (A * (F.identity v u δ).record.size) :=
        mul_le_mul_right (Finset.sum_le_sum (fun I _ => hjet δ hd I)) _
      _ = ENNReal.ofReal (2 ^ (d.1 - 1) * A *
          (‖(F.identity v u δ).map‖ * (F.identity v u δ).record.size)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
          mul_nonneg hA (F.identity v u δ).record.size_nonneg)]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          DerivativeWord2, DerivativeWord, Fintype.card_fun, Fintype.card_fin,
          Nat.cast_pow, Nat.cast_ofNat]
        rw [← ENNReal.ofReal_mul (norm_nonneg _)]
        congr 1
        ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hdegree : d.1 - 1 ≤ cap := (Nat.sub_le d.1 1).trans (hd.trans (hcap v u δ))
        have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdegree
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hA)
          (mul_nonneg (norm_nonneg _) (F.identity v u δ).record.size_nonneg)

/-- Only cap+1 degree slots can contribute, even when the ambient degree is larger. -/
theorem weak_source_fixed_cap_envelope (F : ChartedFamily ι h D P Ctx)
    (cap : ℕ) (hcap : ∀ v u (δ : F.Γ v u), (F.identity v u δ).maxOrder ≤ cap)
    (p : P) (ctx : Ctx p) (π : ι → ℝ) (S : Set ℝ) (clock lam : ℝ)
    (A : ℕ → ℕ → ℝ) (hA : ∀ r q, 0 ≤ A r q) (qs qf : ℕ)
    (Θ : ℝ) (hrow : ∀ v, ∑ u, recordMajorant π F v u ≤ Θ)
    (hcol : ∀ u, ∑ v, recordMajorant π F v u ≤ Θ)
    (hjet : ∀ v u (δ : F.Γ v u) d, d ≤ (F.identity v u δ).maxOrder → ∀ I,
      ∀ r ≤ qs, ∀ q ≤ qf,
      jetSup S r q (fun t X z => F.flux p ctx v u δ d I (clock * t) (lam • X) z) ≤
        ENNReal.ofReal (A r q * (F.identity v u δ).record.size)) :
    IsScaledJetEnvelope π (liftEdges clock lam (F.fiber p ctx)) S 1
      (fun r q => ((cap + 1 : ℕ) : ℝ) * 2 ^ cap * A r q)
      qs qf (recordMajorant π F) Θ := by
  refine ⟨?_, hrow, hcol, ?_⟩
  · intro v u
    exact mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun δ _ =>
      mul_nonneg (norm_nonneg _) (F.identity v u δ).record.size_nonneg)
  · intro v u r hr q hq
    let T (d : Finset.Icc 2 D) : ℝ≥0∞ :=
      (((liftEdges clock lam (F.fiber p ctx)) v u d).map fun γ =>
        ENNReal.ofReal ‖γ.map‖ * ∑ I, jetSup S r q (γ.coeff I)).sum
    let degrees := Finset.univ.filter (fun d : Finset.Icc 2 D => d.1 ≤ cap)
    have hempty (d : Finset.Icc 2 D) (hd : ¬d.1 ≤ cap) : T d = 0 := by
      have he : F.fiber p ctx v u d = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro δ _
        have hn : ¬d.1 ≤ (F.identity v u δ).maxOrder := fun hh => hd (hh.trans (hcap v u δ))
        simp only [hn, dite_false]
      simp only [T, liftEdges, he, List.map_nil, List.sum_nil]
    have hsum : ∑ d, T d = ∑ d ∈ degrees, T d := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun d _ => ?_
      split_ifs with hd
      · rfl
      · exact hempty d hd
    have hcard : degrees.card ≤ cap + 1 := by
      have hinj : Function.Injective (fun d : Finset.Icc 2 D => d.1) := Subtype.val_injective
      rw [← Finset.card_image_of_injective degrees hinj]
      apply le_trans (Finset.card_le_card (show degrees.image (fun d => d.1) ⊆
          Finset.range (cap + 1) from ?_)) (by rw [Finset.card_range])
      intro k hk
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hd).2)
    have hprice : 0 ≤ ∑ δ, ‖(F.identity v u δ).map‖ * (F.identity v u δ).record.size :=
      Finset.sum_nonneg fun δ _ => mul_nonneg (norm_nonneg _) (F.identity v u δ).record.size_nonneg
    have hterms : ∑ d, T d ≤ ENNReal.ofReal
        (((cap + 1 : ℕ) : ℝ) * 2 ^ cap * A r q *
          ∑ δ, ‖(F.identity v u δ).map‖ * (F.identity v u δ).record.size) := by
      rw [hsum]
      calc
        _ ≤ ∑ _d ∈ degrees, ENNReal.ofReal (2 ^ cap * A r q *
            ∑ δ, ‖(F.identity v u δ).map‖ * (F.identity v u δ).record.size) :=
          Finset.sum_le_sum fun d _ => weak_liftedFiber_fixed_cap_price F cap hcap p ctx v u d
            S clock lam (A r q) (hA r q) r q (fun δ hd I => hjet v u δ d.1 hd I r hr q hq)
        _ = ENNReal.ofReal ((degrees.card : ℝ) * (2 ^ cap * A r q *
            ∑ δ, ‖(F.identity v u δ).map‖ * (F.identity v u δ).record.size)) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
            mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (hA r q)) hprice)]
          simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hc : (degrees.card : ℝ) ≤ (cap + 1 : ℕ) := by exact_mod_cast hcard
          exact (mul_le_mul_of_nonneg_right hc
            (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (hA r q)) hprice)).trans_eq
              (by ring)
    apply (mul_le_mul_right hterms _).trans_eq
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    simp only [one_pow, mul_one, recordMajorant]
    congr 1
    ring

end AVRegularity.Finite.WeakLift
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal Classical
namespace AVRegularity.Finite.WeakLift

/-! Radius-generic data for weak and terminal positive-response transfers. Numeric requests are chosen
before data; a slot lift retains the actual native operator through metric, drift and
source identities, including an effective degree cap independent of the ambient cap. -/

open Construction.Preservation.FullLift CycleComparison.Lift EntryWeakProofs

/-- Numeric choices, independent of the terminal level, data, phase and component family. -/
structure WeakPositiveParameters (N H U : ℕ) where
  capMax : ℕ
  cap_ge : 2 ≤ capMax
  slowOrder : ℕ
  fastOrder : ℕ
  slow_reserve : U + (N + capMax) ≤ slowOrder + 4 * (H + 1) * (N + 2) ^ 2
  fast_reserve : U ≤ fastOrder
  CG : ℕ → ℝ
  Cw : ℕ → ℝ
  Cj : ℕ → ℕ → ℝ
  S : ℝ
  S_nonneg : 0 ≤ S
  chartC : ℝ
  chartC_ge : 1 ≤ chartC

def weakSlotLeft (D : OCData) (i : ℕ) (slot : ℤ) : ℝ :=
  D.slotStart i slot / D.cellScaleSq i

def weakSlotRight (D : OCData) (i : ℕ) (slot : ℤ) : ℝ :=
  (((slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i) / D.cellScaleSq i

def weakPositiveNativeData {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (i : ℕ) (G : GenStage D ScalarH Dm bw j₀) (slot : OddSlot)
    (ρ : ℝ := D.eps (i - 1)) :=
  familyLiftData D i slot.1 (nativeChain i slot.1) ρ
    (G.fam.fiber slot (G.actual slot))

/-- A time clamp inherits native fast independence on subsets of its original window. -/
theorem weakPositive_windowEdges_fast {ι : Type*} {hv : ι → Type*}
    [∀ v, NormedAddCommGroup (hv v)] [∀ v, NormedSpace ℝ (hv v)] {Dm : ℕ}
    (edge : ConstituentEdges Dm hv) (a b : ℝ) (S : Set ℝ) (hS : S ⊆ Set.Icc a b)
    (hfast : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsFastIndependentOn S (γ.coeff α)) :
    ∀ v u d, ∀ γ ∈ windowEdges a b edge v u d, ∀ α, IsFastIndependentOn S (γ.coeff α) := by
  intro v u d γ hγ α t ht X z z'
  obtain ⟨δ, hδ, rfl⟩ := List.mem_map.mp hγ
  change δ.coeff α (max a (min b t)) X z = δ.coeff α (max a (min b t)) X z'
  rw [min_eq_right (hS ht).2, max_eq_right (hS ht).1]
  exact hfast v u d δ hδ α t ht X z z'

/-- A capped, window-extended setting with the literal native metric, drift and polynomial
source on the original window. `cap` may exceed a small ambient cap: missing degrees are
zero, rather than an artificial hypothesis `2 ≤ Dm` in the statement. -/
structure WeakPositiveSlot {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    {N H U : ℕ} (P : WeakPositiveParameters N H U) (i : ℕ)
    (G : GenStage D ScalarH Dm bw j₀) (π : CompIn G.comps → ℝ) (slot : OddSlot)
    (ρ : ℝ := D.eps (i - 1)) where
  cap : ℕ
  cap_ge : 2 ≤ cap
  cap_le : cap ≤ P.capMax
  Q : LiftOperatorData (CompIn G.comps) (fun v => ScalarH v.1.root) cap
  price : CompIn G.comps → CompIn G.comps → ℝ
  metric_eq : Q.G = (weakPositiveNativeData i G slot ρ).G
  drift_eq : Q.v = (weakPositiveNativeData i G slot ρ).v
  eta_eq : Q.η = (weakPositiveNativeData i G slot ρ).η
  edge_agree :
    ((∀ v u d, Q.edge v u d = []) ∧
      ∀ v u d, (weakPositiveNativeData i G slot ρ).edge v u d = []) ∨
    ∃ hcap : cap ≤ Dm,
      (∀ v u (d : Finset.Icc 2 Dm), cap < d.1 →
        (weakPositiveNativeData i G slot ρ).edge v u d = []) ∧
      ∀ t ∈ Set.Icc (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1),
        EntryWeakProofs.SlowOpenEdgeEq Set.univ t
          (EntryWeakProofs.restrictConstituentEdges cap hcap
            (weakPositiveNativeData i G slot ρ).edge) Q.edge
  source_eq : ∀ (Cc : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (a₀ : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root) (hh n : ℕ) (_hn : n ≤ N)
    (t : ℝ), t ∈ Set.Icc (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) → ∀ X z,
      liftCellSource Q Cc a₀ hh n t X z =
        liftCellSource (weakPositiveNativeData i G slot ρ) Cc a₀ hh n t X z
  setting : IsLiftSetting Q π (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1)
    (D.eps i) (D.kap i) (D.kap (i - 1)) ρ
    (D.eps (i - 1)) (D.eps i / Real.sqrt (D.kap i))
    (ocDStar D.q D.Λ i (D.kap i) (D.kap (i - 1)))
    (ocDStar D.q D.Λ i (D.kap i) (D.kap (i - 1)) / ρ) (ρ / D.eps (i - 1))
    (pulseParallel slot.1) (pulseShearProfile D.α D.q D.Λ i D.ζ (D.kap i) slot.1)
    H N P.slowOrder P.fastOrder P.fastOrder
    (P.slowOrder + 4 * (H + 1) * (N + cap) ^ 2)
    (max P.fastOrder (P.fastOrder + 2) + H * cap + 2 * N + 2 * cap)
    P.CG P.Cw P.Cj price P.S
  coeff : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)
  sequence : IsLiftSequence Q (P.slowOrder + cap + 2)
    (max (P.fastOrder + 1) (P.fastOrder + 2))
    (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) N H coeff

  /-- Native fast independence passes to the slot lift on every subset of its original window. -/
  edge_fast : ∀ S ⊆ Set.Icc (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1),
    (∀ v u d, ∀ γ ∈ (weakPositiveNativeData i G slot ρ).edge v u d, ∀ α,
      IsFastIndependentOn S (γ.coeff α)) →
    ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α, IsFastIndependentOn S (γ.coeff α)

  /-- Literal ambient-cap recurrence, returned with the effective sequence by the shared lift. -/
  ambient : IsLiftSequence (weakPositiveNativeData i G slot ρ) (P.slowOrder + cap + 2)
    (max (P.fastOrder + 1) (P.fastOrder + 2))
    (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) N H coeff

def weakPositiveMatrix {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {N H U : ℕ}
    {P : WeakPositiveParameters N H U} {i : ℕ} {G : GenStage D ScalarH Dm bw j₀}
    {π : CompIn G.comps → ℝ} {slot : OddSlot} {ρ : ℝ}
    (A : WeakPositiveSlot P i G π slot ρ) (hh : ℕ) :=
  fun v u => nativeLiftScalarBudget U (max P.fastOrder (P.fastOrder + 2)) P.capMax H N
    P.CG P.Cw P.Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π A.price) hh v u

def weakPositivePathCost {N H U : ℕ} (P : WeakPositiveParameters N H U) : ℝ :=
  nativeLiftScalarBudget U (max P.fastOrder (P.fastOrder + 2)) P.capMax H N
    P.CG P.Cw P.Cj * ∑ hh ∈ Finset.range (H + 1), P.S ^ hh

/-- Actual global stream geometry and active original-slot chart jets at a selected lift radius, including the terminal level. -/
structure PositivePhysicalGeometry {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {N U : ℕ}
    (chartC : ℝ) (i : ℕ) (G : GenStage D ScalarH Dm bw j₀)
    (ρ : ℝ := D.eps (i - 1)) : Prop where
  level : G.level = i
  q_gt : 1 < D.q
  Λ_ge : 128 ≤ D.Λ
  fast : IsFastProfile D.ζ
  stream : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ
  band : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ
  plateau : D.term ≤ i
  torus : IsTorusCompatible G.fam G.actual (D.eps (i - 1))
  forward : ∀ (t : ℝ) (slot : OddSlot), ocCutoff D.α D.q D.Λ i slot.1 t ≠ 0 →
    ChartTransport.JetBound (fun x => D.flowOf (i - 1) t x (D.slotAnchor i slot.1))
      (U + N) chartC ρ
  backward : ∀ (t : ℝ) (slot : OddSlot), ocCutoff D.α D.q D.Λ i slot.1 t ≠ 0 →
    ChartTransport.JetBound (fun x => D.flowOf (i - 1) (D.slotAnchor i slot.1) x t)
      (U + N) chartC ρ

/-- The weak menu fixes its geometry orders and chart constant; the other slot-lift parameters do
not enter the physical geometry predicate. -/
abbrev WeakPositiveGeometry {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {N H U : ℕ}
    (P : WeakPositiveParameters N H U) (i : ℕ) (G : GenStage D ScalarH Dm bw j₀)
    (ρ : ℝ := D.eps (i - 1)) : Prop :=
  PositivePhysicalGeometry (N := N) (U := U) P.chartC i G ρ

def WeakPositiveGraded {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {N H U : ℕ}
    {P : WeakPositiveParameters N H U} {i : ℕ} {G : GenStage D ScalarH Dm bw j₀}
    {π : CompIn G.comps → ℝ} {slot : OddSlot} {ρ : ℝ}
    (A : WeakPositiveSlot P i G π slot ρ) : Prop :=
  ∀ hh, hh ≤ H → ∀ n, n ≤ N →
    AmbientLiftCoefficientData (pulseParallel slot.1) (weakSlotLeft D i slot.1)
      (weakSlotRight D i slot.1) A.setting.window (ρ / D.eps (i - 1)) n U U (A.coeff hh n)
      (weakPositiveMatrix A hh)

/-- Identification is on the original window, not an unjustified equality outside it.
Positive tested order removes the input-amplitude coefficient at m=0. -/
def WeakPositiveIdentified {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {N H U : ℕ}
    {P : WeakPositiveParameters N H U} {i : ℕ} {G : GenStage D ScalarH Dm bw j₀}
    {π : CompIn G.comps → ℝ} {slot : OddSlot} {ρ : ℝ}
    (A : WeakPositiveSlot P i G π slot ρ)
    (Cc : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)) : Prop :=
  (∀ hh, hh ≤ H → ∀ n m (a : DerivativeWord2 m) t,
    t ∈ Set.Icc (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) → ∀ X z v u,
      Cc hh n m a t X z v u = A.coeff hh n m a t X z v u) ∧
  (∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ a : DerivativeWord2 0, ∀ t,
    t ∈ Set.Icc (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1) → ∀ X z v u,
      A.coeff hh n 0 a t X z v u = 0)

end AVRegularity.Finite.WeakLift
end
