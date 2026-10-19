-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeak.SobolevSummableMajorantBound
public import AVRegularity.Proofs.Majorant.Unique
public import AVRegularity.EntryWeak.JointSourceCongruence
public import AVRegularity.Proofs.GenSem.LiftGen.Drift
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set Filter Topology Metric
namespace AVRegularity.Providers.WeakGen

/-! Compact local jet bounds give genuine global forcing reserves after slow cutoff and
clamping to the original time window. Fast periodicity removes the unbounded fast variable. -/

open AVRegularity.EntryWeakProofs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every joint derivative has the same fast period as the original source. -/
theorem periodic_joint_jet (f : ℝ → Vec 2 → Vec 2 → E)
    (hp : ∀ t Y, AVenhance.IsZ2Periodic (fun z => f t z Y))
    (n : ℕ) (t : ℝ) (Y z : Vec 2) (k : Fin 2 → ℤ) :
    iteratedFDeriv ℝ n (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2)
        (z + AVenhance.latticeShift k, Y) =
      iteratedFDeriv ℝ n (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) (z, Y) := by
  have he : (fun Z : Vec 2 × Vec 2 =>
      f t (Z + (AVenhance.latticeShift k, 0)).1 (Z + (AVenhance.latticeShift k, 0)).2) =
      (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) := by
    funext Z
    simpa only [Prod.fst_add, Prod.snd_add, add_zero] using hp t Z.2 k Z.1
  have h := congrArg (fun g => iteratedFDeriv ℝ n g (z, Y)) he
  have ht := iteratedFDeriv_comp_add_right (𝕜 := ℝ)
    (f := fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) n (AVenhance.latticeShift k, 0) (z, Y)
  have hadd : (z, Y) + (AVenhance.latticeShift k, 0) =
      (z + AVenhance.latticeShift k, Y) := by ext <;> simp
  rw [hadd] at ht
  exact ht.symm.trans h

/-- A compact jet bound on one fast cell controls every fast point. -/
theorem periodic_joint_jet_bound (f : ℝ → Vec 2 → Vec 2 → E)
    (hp : ∀ t Y, AVenhance.IsZ2Periodic (fun z => f t z Y))
    (T : Set ℝ) (U : Set (Vec 2)) (n : ℕ) (B : ℝ)
    (hb : ∀ t ∈ T, ∀ X ∈ AVenhance.Infra.Torus.Calculus.closedUnitCell 2 ×ˢ closure U,
      ‖iteratedFDeriv ℝ n (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) X‖ ≤ B) :
    ∀ t ∈ T, ∀ X : Vec 2 × Vec 2, X.2 ∈ U →
      ‖iteratedFDeriv ℝ n (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) X‖ ≤ B := by
  intro t ht X hX
  let k : Fin 2 → ℤ := fun i => ⌊X.1 i⌋
  let z : Vec 2 := fun i => Int.fract (X.1 i)
  have hz : z ∈ AVenhance.Infra.Torus.Calculus.closedUnitCell 2 :=
    fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have he : X.1 = z + AVenhance.latticeShift k := by
    funext i
    exact (Int.fract_add_floor (X.1 i)).symm
  have hj := periodic_joint_jet f hp n t X.2 z k
  rw [← he] at hj
  exact (congrArg norm hj).le.trans (hb t ht (z, X.2) ⟨hz, subset_closure hX⟩)

variable [MeasurableSpace E] [BorelSpace E]

/-- Local compact jets, measurable only on the solving window, suffice for a cutoff reserve. -/
theorem compact_window_cutoff_reserve (H : ℕ) (a b : ℝ) (hab : a ≤ b)
    (Ω U : Set (Vec 2)) (hU : IsOpen U)
    (hK : IsCompact (closure U)) (hsub : closure U ⊆ Ω)
    (χ : Vec 2 → ℝ) (hs : tsupport χ ⊆ U)
    (Qχ : JointSourceReserve H (fun _ _ Y => χ Y))
    (f : ℝ → Vec 2 → Vec 2 → E)
    (hf : ∀ t ∈ Icc a b, ContDiffOn ℝ (H : ℕ∞)
      (fun X : Vec 2 × Vec 2 => f t X.1 X.2) {X | X.2 ∈ Ω})
    (hp : ∀ t Y, AVenhance.IsZ2Periodic (fun z => f t z Y))
    (hm : ∀ Y ∈ Ω, Measurable (fun Z : Icc a b × Vec 2 => f Z.1 Z.2 Y))
    (hb : ∀ (K : Set (Vec 2 × Vec 2)), IsCompact K → K ⊆ {X | X.2 ∈ Ω} → ∀ n,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ X ∈ K,
        ‖iteratedFDeriv ℝ n (fun Z : Vec 2 × Vec 2 => f t Z.1 Z.2) X‖ ≤ B) :
    Nonempty (JointSourceReserve H (fun t z Y => χ Y • f (max a (min b t)) z Y)) := by
  classical
  have hjet := hb (AVenhance.Infra.Torus.Calculus.closedUnitCell 2 ×ˢ closure U)
    ((AVenhance.Infra.Torus.Calculus.isCompact_closedUnitCell 2).prod hK)
    (fun _ hx => hsub hx.2)
  choose B hB hbound using hjet
  have huΩ : U ⊆ Ω := subset_closure.trans hsub
  have hmem t : max a (min b t) ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  let clamp : ℝ → Icc a b := fun t => ⟨max a (min b t), hmem t⟩
  have hc : Measurable clamp :=
    (measurable_const.max (measurable_const.min measurable_id)).subtype_mk
  exact ⟨cutoffSourceReserve H U hU χ hs Qχ (fun t z Y => f (clamp t) z Y)
    (fun t => (hf _ (hmem t)).mono (fun _ hY => huΩ hY))
    (fun t Y _ => hp (clamp t) Y)
    (fun Y hY => (hm Y (huΩ hY)).comp ((hc.comp measurable_fst).prodMk measurable_snd))
    B hB (fun n _ t X hX => periodic_joint_jet_bound f hp (Icc a b) U n (B n)
      (hbound n) _ (hmem t) X hX)⟩

end AVRegularity.Providers.WeakGen
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen

/-! **Lift data across order caps** (weak entry). The order cap `D` of a lift operator
(`LiftOperatorData ι h D`, edges of the orders `2 ≤ d ≤ D`) is a bound, not a datum. When the edges
vanish above an order `N ≤ D` (`EdgesBelow`), the restriction of the edges to the orders `≤ N`
(`restrictEdges`, `restrictData`) has the same source flux (`sourceFlux_restrict`), hence the same
source operators, cell arrays, means and cell sources at every degree `n ≤ N`. So the same
coefficients are lift sequences (`isLiftSequenceOn_restrict`, `isLiftSequence_restrict`), and the
path means of degree `n ≤ N` agree (`pathMeanFlux_restrict`). The weak stages have all their orders
`≤ 1 + J_w N_w`, a cap independent of the stage cap `Dm`; this lets the energy estimates run with
constants uniform in `Dm`. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The order `d ≤ N` as an order `≤ D`. -/
def capOrder {D N : ℕ} (hN : N ≤ D) (d : Finset.Icc 2 N) : Finset.Icc 2 D :=
  ⟨d.1, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp d.2).1, (Finset.mem_Icc.mp d.2).2.trans hN⟩⟩

/-- The edges restricted to the orders `≤ N`. -/
def restrictEdges {D N : ℕ} (hN : N ≤ D) (edge : ConstituentEdges D h) : ConstituentEdges N h :=
  fun v u d => edge v u (capOrder hN d)

/-- The edges vanish above the order `N`. -/
def EdgesBelow (N : ℕ) {D : ℕ} (edge : ConstituentEdges D h) : Prop :=
  ∀ v u (d : Finset.Icc 2 D), N < d.1 → edge v u d = []

/-- The lift operator data with the edges restricted to the orders `≤ N`. -/
def restrictData {D N : ℕ} (hN : N ≤ D) (Q : LiftOperatorData ι h D) : LiftOperatorData ι h N :=
  ⟨Q.η, Q.G, Q.v, restrictEdges hN Q.edge⟩

omit [Fintype ι] in
/-- The lifted edges vanish above `N` with the edges. -/
theorem edgesBelow_liftEdges {D N : ℕ} {edge : ConstituentEdges D h} (hE : EdgesBelow N edge)
    (c lam : ℝ) :
    EdgesBelow N (liftEdges c lam edge) := fun v u d hd => by
  simp only [liftEdges, hE v u d hd, List.map_nil]

/-- A sum over the orders `≤ D` of a function vanishing above `N` is its sum over the orders
`≤ N`. -/
theorem sum_capOrder {M : Type*} [AddCommMonoid M] {D N : ℕ} (hN : N ≤ D)
    (f : Finset.Icc 2 D → M) (hf : ∀ d : Finset.Icc 2 D, N < d.1 → f d = 0) :
    ∑ d : Finset.Icc 2 N, f (capOrder hN d) = ∑ d : Finset.Icc 2 D, f d := by
  classical
  set g : ℕ → M := fun x => if hx : x ∈ Finset.Icc 2 D then f ⟨x, hx⟩ else 0 with hg
  have hD : ∑ d : Finset.Icc 2 D, f d = ∑ x ∈ Finset.Icc 2 D, g x := by
    rw [← Finset.sum_attach (Finset.Icc 2 D) g, Finset.univ_eq_attach]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hg, d.2, ↓reduceDIte]
  have hN' : ∑ d : Finset.Icc 2 N, f (capOrder hN d) = ∑ x ∈ Finset.Icc 2 N, g x := by
    rw [← Finset.sum_attach (Finset.Icc 2 N) g, Finset.univ_eq_attach]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hd : d.1 ∈ Finset.Icc 2 D := (capOrder hN d).2
    simp only [hg, hd, ↓reduceDIte]
    rfl
  rw [hD, hN']
  refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN) fun x hx hxN => ?_
  have hxN' : N < x := by
    by_contra hc
    exact hxN (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1, not_lt.mp hc⟩)
  simp only [hg, hx, ↓reduceDIte]
  exact hf ⟨x, hx⟩ hxN'

/-- **The source flux of the restricted edges.** -/
theorem sourceFlux_restrict {D N : ℕ} (hN : N ≤ D) (edge : ConstituentEdges D h)
    (hE : EdgesBelow N edge) (η ε t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2) :
    sourceFlux (restrictEdges hN edge) η ε t Φ k = sourceFlux edge η ε t Φ k := by
  funext X z v
  unfold sourceFlux
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← sum_capOrder hN (fun d : Finset.Icc 2 D => ((edge v u d).map fun γ =>
      ∑ α : DerivativeWord2 (d.1 - 1), (γ.coeff α t X z k) • γ.map (dEpsWord η ε α Φ X z u)).sum)
    (fun d hd => by rw [hE v u d hd]; rfl)]
  rfl

theorem sourceOp_restrict {D N : ℕ} (hN : N ≤ D) (edge : ConstituentEdges D h)
    (hE : EdgesBelow N edge) (η ε t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) :
    sourceOp (restrictEdges hN edge) η ε t Φ = sourceOp edge η ε t Φ := by
  unfold sourceOp
  simp only [sourceFlux_restrict hN edge hE]

theorem sourceCoeff_restrict {D N : ℕ} (hN : N ≤ D) (edge : ConstituentEdges D h)
    (hE : EdgesBelow N edge) (η : ℝ) (j : ℕ) (t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) :
    sourceCoeff (restrictEdges hN edge) η j t Φ = sourceCoeff edge η j t Φ := by
  unfold sourceCoeff
  simp only [sourceOp_restrict hN edge hE]

variable {D N : ℕ} (hN : N ≤ D) {Q : LiftOperatorData ι h D} (hE : EdgesBelow N Q.edge)
  (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i)

include hE in
theorem liftA_restrict (hh : ℕ) {n : ℕ} (hn : n ≤ N) :
    liftA (restrictData hN Q) Cc a hh n = liftA Q Cc a hh n := by
  funext t X z
  have h1 : min N n = n := Nat.min_eq_right hn
  have h2 : min D n = n := Nat.min_eq_right (hn.trans hN)
  simp only [liftA, restrictData, h1, h2, sourceCoeff_restrict hN Q.edge hE]

include hE in
theorem liftMean_restrict (hh : ℕ) {n : ℕ} (hn : n ≤ N) :
    liftMean (restrictData hN Q) Cc a hh n = liftMean Q Cc a hh n := by
  funext t X
  simp only [liftMean, liftA_restrict hN hE Cc a hh hn]

include hE in
theorem liftCellSource_restrict (hh : ℕ) {n : ℕ} (hn : n ≤ N) :
    liftCellSource (restrictData hN Q) Cc a hh n = liftCellSource Q Cc a hh n := by
  have hS : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftMean (restrictData hN Q) Cc a p.2 (n - j) = liftMean Q Cc a p.2 (n - j) :=
    fun j _ p _ => liftMean_restrict hN hE Cc a p.2 (by omega)
  have hA := liftA_restrict hN hE Cc a hh hn
  have hM := liftMean_restrict hN hE Cc a hh hn
  funext t X z
  unfold liftCellSource
  rw [hA, hM]
  exact congrArg _ (Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun p hp => by
    rw [hS j hj p hp])

include hE in
theorem liftFluxX_restrict (hh : ℕ) {n : ℕ} (hn : n ≤ N) :
    liftFluxX (restrictData hN Q) Cc a hh n = liftFluxX Q Cc a hh n := by
  funext t X z k
  have h1 : min N n = n := Nat.min_eq_right hn
  have h2 : min D n = n := Nat.min_eq_right (hn.trans hN)
  simp only [liftFluxX, restrictData, h1, h2, sourceFlux_restrict hN Q.edge hE]

variable [∀ i, FiniteDimensional ℝ (h i)]

include hE in
/-- **The lift sequences of the restricted data** (localized). -/
theorem isLiftSequenceOn_restrict {Ω : Set (Vec 2)} {sX sZ : ℕ} {t₀ t₁ : ℝ} {Nl H : ℕ}
    (hNl : Nl ≤ N) (hC : IsLiftSequenceOn Ω Q sX sZ t₀ t₁ Nl H Cc) :
    IsLiftSequenceOn Ω (restrictData hN Q) sX sZ t₀ t₁ Nl H Cc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hC
  refine ⟨h1, h2, h3, h4, h5, h6, fun hh hhH n hn1 hnN a₀ ha₀ X hX => ?_⟩
  rw [liftCellSource_restrict hN hE Cc _ hh (hnN.trans hNl)]
  exact h7 hh hhH n hn1 hnN a₀ ha₀ X hX

include hE in
/-- **The lift sequences of the restricted data.** -/
theorem isLiftSequence_restrict {sX sZ : ℕ} {t₀ t₁ : ℝ} {Nl H : ℕ}
    (hNl : Nl ≤ N) (hC : IsLiftSequence Q sX sZ t₀ t₁ Nl H Cc) :
    IsLiftSequence (restrictData hN Q) sX sZ t₀ t₁ Nl H Cc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hC
  refine ⟨h1, h2, h3, h4, h5, h6, fun hh hhH n hn1 hnN a₀ ha₀ X => ?_⟩
  rw [liftCellSource_restrict hN hE Cc _ hh (hnN.trans hNl)]
  exact h7 hh hhH n hn1 hnN a₀ ha₀ X

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- **The path means of degree `≤ N` of the restricted data.** -/
theorem pathMeanFlux_restrict (Dd : OCData) (m : ℕ) (ρ : ℝ) {hp : ℕ}
    {Q : LiftOperatorData (Fin (hp + 1)) (fun _ => ℝ) D} (hE : EdgesBelow N Q.edge)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (hp + 1)) (fun _ => ℝ)) {n : ℕ} (hn : n ≤ N) (t : ℝ) :
    pathMeanFlux Dd m ρ (restrictData hN Q) Cc n t = pathMeanFlux Dd m ρ Q Cc n t := by
  funext f y k
  simp only [pathMeanFlux, liftFluxX_restrict hN hE Cc _ hp hn]

end AVRegularity.Providers.WeakGen
end

section
open Homogenization AVRegularity
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen

/-! **The nonzero modes scale with the drift** (weak entry, eddy ledger). Give the child-frame
geometric letters and the child evaluations the trivial profile `⊤` as leaves (`leafTop`); then the
only letters with nonzero modes are the drift letters, since the own-frame geometric letters and the
time letters are zero-mode letters. So if the drift profiles are scaled by `λ ≤ 1`, every nonzero
mode of the structural majorant of any expression is scaled by at least `λ`
(`genMode_drift_scale`); the zero modes only decrease. Replacing leaves by `⊤` only increases the
majorant (`genMode_le_leafTop`).

At a weak level the drift constant of the passage is the Péclet number `Pe_i`, and the graded
calculus of the ledger at the uniform constant `C_pe ≥ Pe_i` bounds the lift coefficients; with
`λ = Pe_i/C_pe` their nonzero modes cost one more factor `Pe_i`. The eddy mean reads only the
modes `±1` of the grade-zero lift, through the drift letter: this gives the second Péclet factor of
the eddy entry. -/

/-- The leaves of the scaling argument: the child-frame geometric letters and the child
evaluations, with the trivial profile. -/
def leafTop : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)
  | _, _, _, .geo (.child _) _ => some fun _ _ => ⊤
  | _, _, _, .evalChild _ _ => some fun _ _ => ⊤
  | _, _, _, _ => none

/-- No leaf. -/
def leafNone : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞) :=
  fun _ => none

@[simp] theorem leafNone_eq {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p) : leafNone e = none := rfl

variable (D : OCData) (Δ : ℝ)

theorem derivCost_mono {C C' : ℝ≥0∞} (hC : C ≤ C') (ε Δ mres : ℝ) {x x' : ℝ≥0∞} (hx : x ≤ x') :
    derivCost C ε Δ mres x ≤ derivCost C' ε Δ mres x' := by
  unfold derivCost
  split_ifs
  · exact mul_le_mul' (ENNReal.div_le_div_right hC _) hx
  · exact le_rfl

theorem derivCost_scale {C C' : ℝ≥0∞} (hC : C ≤ C') (ε Δ mres : ℝ) {lam x x' : ℝ≥0∞}
    (hl : lam ≠ 0) (hx : x ≤ lam * x') :
    derivCost C ε Δ mres x ≤ lam * derivCost C' ε Δ mres x' := by
  unfold derivCost
  split_ifs
  · calc C / ENNReal.ofReal (ε * Δ) * x ≤ C' / ENNReal.ofReal (ε * Δ) * (lam * x') :=
          mul_le_mul' (ENNReal.div_le_div_right hC _) hx
      _ = lam * (C' / ENNReal.ofReal (ε * Δ) * x') := by ring
  · rw [ENNReal.mul_top hl]

/-- **Leaves of trivial profile only increase the majorant.** -/
theorem genMode_le_leafTop (κ : MajConsts) :
    ∀ {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p) (mres : ℝ) (h : ℤ) (t : ℝ),
      genMode D κ Δ leafNone e mres h t ≤ genMode D κ Δ leafTop e mres h t := by
  intro s i p e
  induction e with
  | geo fr L =>
    intro mres h t
    cases fr with
    | own => exact le_rfl
    | child p' => simp [genMode, leafTop]
  | drift c => intro mres h t; exact le_rfl
  | time L => intro mres h t; exact le_rfl
  | add a b iha ihb =>
    intro mres h t
    simp only [genMode, leafNone, leafTop, Option.elim]
    exact add_le_add (iha mres h t) (ihb mres h t)
  | mul a b iha ihb =>
    intro mres h t
    simp only [genMode, leafNone, leafTop, Option.elim]
    exact ENNReal.tsum_le_tsum fun k => mul_le_mul' (iha mres k t) (ihb mres (h - k) t)
  | dOld j a ih =>
    intro mres h t
    simp only [genMode, leafNone, leafTop, Option.elim]
    exact add_le_add (derivCost_mono le_rfl _ _ _ (ih _ h t)) (mul_le_mul' le_rfl (ih mres h t))
  | dPhase a ih =>
    intro mres h t
    simp only [genMode, leafNone, leafTop, Option.elim]
    exact mul_le_mul' le_rfl (ih mres h t)
  | dSlowFam j a ih =>
    intro mres h t
    simp only [genMode, leafNone, leafTop, Option.elim]
    exact derivCost_mono le_rfl _ _ _ (ih _ h t)
  | dSlowCell j a ih =>
    intro mres h t
    simp only [genMode, leafNone, leafTop, Option.elim]
    exact derivCost_mono le_rfl _ _ _ (ih _ h t)
  | dInternal a ih =>
    intro mres h t
    simp only [genMode, leafNone, leafTop, Option.elim]
    exact mul_le_mul' le_rfl (ih mres h t)
  | restrict a ih =>
    intro mres h t
    simp only [genMode, leafNone, leafTop, Option.elim]
    exact ih mres h t
  | cellInv F t₀ ι ihF ihι =>
    intro mres h t
    simp only [genMode, leafNone, leafTop, Option.elim]
    exact add_le_add (ihι mres h t₀) (mul_le_mul' le_rfl (iSup₂_mono fun s _ => ihF _ mres h s))
  | transPrim a ih =>
    intro mres h t
    simp only [genMode, leafNone, leafTop, Option.elim]
    exact mul_le_mul' le_rfl (ih mres h t)
  | solved => intro mres h t; exact le_rfl
  | mean a ih =>
    intro mres h t
    simp only [genMode, leafNone, leafTop, Option.elim]
    split_ifs
    · exact ih mres 0 t
    · exact le_rfl
  | famCell a ih =>
    intro mres h t
    simp only [genMode, leafNone, leafTop, Option.elim]
    split_ifs
    · exact ih mres 0 t
    · exact le_rfl
  | evalChild p' c ih => intro mres h t; simp [genMode, leafTop]

/-- **The nonzero modes scale with the drift profiles.** If the drift profiles of `κ` are at most
`λ` times those of `κ'`, and the two agree (up to `≤`) on the own-frame geometric letters, which are
zero-mode letters, and on the Cauchy constants, then with the leaves `leafTop` every mode of the
majorant at `κ` is at most that at `κ'`, and every nonzero mode at most `λ` times it. -/
theorem genMode_drift_scale {κ κ' : MajConsts} {lam : ℝ≥0∞} (hl0 : lam ≠ 0) (hl1 : lam ≤ 1)
    (hd : ∀ c h, κ.drift c h ≤ lam * κ'.drift c h)
    (hg : ∀ L h, κ.geo .own L h ≤ κ'.geo .own L h) (hg0 : ∀ L h, h ≠ 0 → κ.geo .own L h = 0)
    (hCold : κ.Cold ≤ κ'.Cold) (hCslow : κ.Cslow ≤ κ'.Cslow) :
    ∀ {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p) (mres : ℝ) (h : ℤ) (t : ℝ),
      genMode D κ Δ leafTop e mres h t ≤ genMode D κ' Δ leafTop e mres h t ∧
        (h ≠ 0 → genMode D κ Δ leafTop e mres h t ≤ lam * genMode D κ' Δ leafTop e mres h t) := by
  have htop : (⊤ : ℝ≥0∞) ≤ lam * ⊤ := by rw [ENNReal.mul_top hl0]
  intro s i p e
  induction e with
  | geo fr L =>
    intro mres h t
    cases fr with
    | own =>
      simp only [genMode, leafTop, Option.elim]
      exact ⟨hg L h, fun hh => by rw [hg0 L h hh]; exact zero_le⟩
    | child p' => simp only [genMode, leafTop, Option.elim]; exact ⟨le_rfl, fun _ => htop⟩
  | drift c =>
    intro mres h t
    simp only [genMode, leafTop, Option.elim]
    exact ⟨(hd c h).trans (mul_le_of_le_one_left (zero_le) hl1), fun _ => hd c h⟩
  | time L =>
    intro mres h t
    simp only [genMode, leafTop, Option.elim]
    refine ⟨le_rfl, fun hh => ?_⟩
    rw [ite_eq_right hh]
    exact zero_le
  | add a b iha ihb =>
    intro mres h t
    simp only [genMode, leafTop, Option.elim]
    refine ⟨add_le_add (iha mres h t).1 (ihb mres h t).1, fun hh => ?_⟩
    rw [mul_add]
    exact add_le_add ((iha mres h t).2 hh) ((ihb mres h t).2 hh)
  | mul a b iha ihb =>
    intro mres h t
    simp only [genMode, leafTop, Option.elim]
    refine ⟨ENNReal.tsum_le_tsum fun k => mul_le_mul' (iha mres k t).1 (ihb mres (h - k) t).1,
      fun hh => ?_⟩
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun k => ?_
    by_cases hk : k = 0
    · subst hk
      have hb := (ihb mres (h - 0) t).2 (by simpa using hh)
      calc genMode D κ Δ leafTop a mres 0 t * genMode D κ Δ leafTop b mres (h - 0) t
          ≤ genMode D κ' Δ leafTop a mres 0 t * (lam * genMode D κ' Δ leafTop b mres (h - 0) t) :=
            mul_le_mul' (iha mres 0 t).1 hb
        _ = _ := by ring
    · calc genMode D κ Δ leafTop a mres k t * genMode D κ Δ leafTop b mres (h - k) t
          ≤ (lam * genMode D κ' Δ leafTop a mres k t) * genMode D κ' Δ leafTop b mres (h - k) t :=
            mul_le_mul' ((iha mres k t).2 hk) (ihb mres (h - k) t).1
        _ = _ := by ring
  | dOld j a ih =>
    intro mres h t
    simp only [genMode, leafTop, Option.elim]
    refine ⟨add_le_add (derivCost_mono hCold _ _ _ (ih _ h t).1)
      (mul_le_mul' le_rfl (ih mres h t).1), fun hh => ?_⟩
    rw [mul_add]
    refine add_le_add (derivCost_scale hCold _ _ _ hl0 ((ih _ h t).2 hh)) ?_
    calc _ ≤ _ * (lam * genMode D κ' Δ leafTop a mres h t) := mul_le_mul' le_rfl ((ih mres h t).2 hh)
      _ = _ := by ring
  | dPhase a ih =>
    intro mres h t
    simp only [genMode, leafTop, Option.elim]
    refine ⟨mul_le_mul' le_rfl (ih mres h t).1, fun hh => ?_⟩
    calc _ ≤ modeMul h * (lam * genMode D κ' Δ leafTop a mres h t) :=
          mul_le_mul' le_rfl ((ih mres h t).2 hh)
      _ = _ := by ring
  | dSlowFam j a ih =>
    intro mres h t
    simp only [genMode, leafTop, Option.elim]
    exact ⟨derivCost_mono hCslow _ _ _ (ih _ h t).1,
      fun hh => derivCost_scale hCslow _ _ _ hl0 ((ih _ h t).2 hh)⟩
  | dSlowCell j a ih =>
    intro mres h t
    simp only [genMode, leafTop, Option.elim]
    exact ⟨derivCost_mono hCslow _ _ _ (ih _ h t).1,
      fun hh => derivCost_scale hCslow _ _ _ hl0 ((ih _ h t).2 hh)⟩
  | dInternal a ih =>
    intro mres h t
    simp only [genMode, leafTop, Option.elim]
    refine ⟨mul_le_mul' le_rfl (ih mres h t).1, fun hh => ?_⟩
    calc _ ≤ modeMul h * (lam * genMode D κ' Δ leafTop a mres h t) :=
          mul_le_mul' le_rfl ((ih mres h t).2 hh)
      _ = _ := by ring
  | restrict a ih =>
    intro mres h t
    simp only [genMode, leafTop, Option.elim]
    exact ih mres h t
  | @cellInv i' p' F t₀ ι ihF ihι =>
    intro mres h t
    simp only [genMode, leafTop, Option.elim]
    refine ⟨add_le_add (ihι mres h t₀).1 (mul_le_mul' le_rfl (iSup₂_mono fun s _ =>
      (ihF _ mres h s).1)), fun hh => ?_⟩
    have hsup : (⨆ s ∈ Set.Icc t₀ t, genMode D κ Δ leafTop (F (transverseIndex p')) mres h s) ≤
        lam * ⨆ s ∈ Set.Icc t₀ t, genMode D κ' Δ leafTop (F (transverseIndex p')) mres h s :=
      iSup₂_le fun s hs => ((ihF _ mres h s).2 hh).trans (mul_le_mul' le_rfl (le_iSup₂ (f := fun
        s (_ : s ∈ Set.Icc t₀ t) => genMode D κ' Δ leafTop (F (transverseIndex p')) mres h s) s hs))
    calc _ ≤ lam * genMode D κ' Δ leafTop ι mres h t₀ + ENNReal.ofReal (4 / 3) * modeGain h *
          (lam * ⨆ s ∈ Set.Icc t₀ t, genMode D κ' Δ leafTop (F (transverseIndex p')) mres h s) :=
          add_le_add ((ihι mres h t₀).2 hh) (mul_le_mul' le_rfl hsup)
      _ = _ := by ring
  | transPrim a ih =>
    intro mres h t
    simp only [genMode, leafTop, Option.elim]
    refine ⟨mul_le_mul' le_rfl (ih mres h t).1, fun hh => ?_⟩
    calc _ ≤ modeGain h * (lam * genMode D κ' Δ leafTop a mres h t) :=
          mul_le_mul' le_rfl ((ih mres h t).2 hh)
      _ = _ := by ring
  | solved => intro mres h t; simp only [genMode, leafTop, Option.elim]; exact ⟨le_rfl, fun _ => htop⟩
  | mean a ih =>
    intro mres h t
    simp only [genMode, leafTop, Option.elim]
    refine ⟨?_, fun hh => ?_⟩
    · split_ifs
      · exact (ih mres 0 t).1
      · exact le_rfl
    · rw [ite_eq_right hh]; exact zero_le
  | famCell a ih =>
    intro mres h t
    simp only [genMode, leafTop, Option.elim]
    refine ⟨?_, fun hh => ?_⟩
    · split_ifs
      · exact (ih mres 0 t).1
      · exact le_rfl
    · rw [ite_eq_right hh]; exact zero_le
  | evalChild p' c ih =>
    intro mres h t; simp only [genMode, leafTop, Option.elim]; exact ⟨le_rfl, fun _ => htop⟩

/-- **Leaves dominating the structural majorant only increase it**: if every leaf profile is
above the leaf-free majorant of its expression, at every time, the leaf-free majorant of every
expression is below its majorant with the leaves. -/
theorem genMode_le_of_leaf_dominates (κ : MajConsts)
    (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞))
    (hL : ∀ {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p) (B : ℝ → ℤ → ℝ≥0∞), leaf e = some B →
      ∀ mres h t, genMode D κ Δ leafNone e mres h t ≤ B mres h) :
    ∀ {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p) (mres : ℝ) (h : ℤ) (t : ℝ),
      genMode D κ Δ leafNone e mres h t ≤ genMode D κ Δ leaf e mres h t := by
  intro s i p e
  induction e with
  | @geo i' p' fr L =>
    intro mres h t
    rcases hle : leaf (Gen.geo (i := i') (p := p') fr L) with _ | B
    · simp [genMode, leafNone_eq, hle]
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | @drift i' p' c =>
    intro mres h t
    rcases hle : leaf (Gen.drift (i := i') (p := p') c) with _ | B
    · simp [genMode, leafNone_eq, hle]
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | @time s' i' p' L =>
    intro mres h t
    rcases hle : leaf (Gen.time (s := s') (i := i') (p := p') L) with _ | B
    · simp [genMode, leafNone_eq, hle]
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | add a b iha ihb =>
    intro mres h t
    rcases hle : leaf (Gen.add a b) with _ | B
    · simp only [genMode, leafNone_eq, hle, Option.elim]
      exact add_le_add (iha mres h t) (ihb mres h t)
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | mul a b iha ihb =>
    intro mres h t
    rcases hle : leaf (Gen.mul a b) with _ | B
    · simp only [genMode, leafNone_eq, hle, Option.elim]
      exact ENNReal.tsum_le_tsum fun k => mul_le_mul' (iha mres k t) (ihb mres (h - k) t)
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | dOld j a ih =>
    intro mres h t
    rcases hle : leaf (Gen.dOld j a) with _ | B
    · simp only [genMode, leafNone_eq, hle, Option.elim]
      exact add_le_add (derivCost_mono le_rfl _ _ _ (ih _ h t)) (mul_le_mul' le_rfl (ih mres h t))
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | dPhase a ih =>
    intro mres h t
    rcases hle : leaf (Gen.dPhase a) with _ | B
    · simp only [genMode, leafNone_eq, hle, Option.elim]
      exact mul_le_mul' le_rfl (ih mres h t)
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | dSlowFam j a ih =>
    intro mres h t
    rcases hle : leaf (Gen.dSlowFam j a) with _ | B
    · simp only [genMode, leafNone_eq, hle, Option.elim]
      exact derivCost_mono le_rfl _ _ _ (ih _ h t)
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | dSlowCell j a ih =>
    intro mres h t
    rcases hle : leaf (Gen.dSlowCell j a) with _ | B
    · simp only [genMode, leafNone_eq, hle, Option.elim]
      exact derivCost_mono le_rfl _ _ _ (ih _ h t)
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | dInternal a ih =>
    intro mres h t
    rcases hle : leaf (Gen.dInternal a) with _ | B
    · simp only [genMode, leafNone_eq, hle, Option.elim]
      exact mul_le_mul' le_rfl (ih mres h t)
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | restrict a ih =>
    intro mres h t
    rcases hle : leaf (Gen.restrict a) with _ | B
    · simp only [genMode, leafNone_eq, hle, Option.elim]
      exact ih mres h t
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | cellInv F t₀ ι ihF ihι =>
    intro mres h t
    rcases hle : leaf (Gen.cellInv F t₀ ι) with _ | B
    · simp only [genMode, leafNone_eq, hle, Option.elim]
      exact add_le_add (ihι mres h t₀) (mul_le_mul' le_rfl (iSup₂_mono fun s _ => ihF _ mres h s))
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | transPrim a ih =>
    intro mres h t
    rcases hle : leaf (Gen.transPrim a) with _ | B
    · simp only [genMode, leafNone_eq, hle, Option.elim]
      exact mul_le_mul' le_rfl (ih mres h t)
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | solved G v F q t₀ t₁ c sZ ι =>
    intro mres h t
    rcases hle : leaf (Gen.solved G v F q t₀ t₁ c sZ ι) with _ | B
    · simp [genMode, leafNone_eq, hle]
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | mean a ih =>
    intro mres h t
    rcases hle : leaf (Gen.mean a) with _ | B
    · simp only [genMode, leafNone_eq, hle, Option.elim]
      split_ifs
      · exact ih mres 0 t
      · exact le_rfl
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | famCell a ih =>
    intro mres h t
    rcases hle : leaf (Gen.famCell a) with _ | B
    · simp only [genMode, leafNone_eq, hle, Option.elim]
      split_ifs
      · exact ih mres 0 t
      · exact le_rfl
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t
  | @evalChild i' p'' p' c ih =>
    intro mres h t
    rcases hle : leaf (Gen.evalChild (i := i') (p := p'') p' c) with _ | B
    · simp only [genMode, leafNone_eq, hle, Option.elim]
      exact mul_le_mul' le_rfl (ih mres 0 t)
    · simpa [genMode, leafNone_eq, hle] using hL _ B hle mres h t

end AVRegularity.Providers.WeakGen
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen

/-! **Mode bounds of the eddy mean** (weak entry).
* `gsumList`: the explicit sum of a list of expressions, with its uniform representation
  (`URep.gsumList`) and the mode bound of its structural majorant (`genMode_gsumList_le`).
* `leafMeanAt κ m`: the family means of the level `m` as leaves, with the profile
  `[h = 0] · sup_t` of their leaf-free majorant at mode `0`. These profiles dominate the leaf-free
  majorant (`leafMeanAt_dominates`), and a constant times a mean has the structural norm
  `|c| · sup_t genMode(mean)` (`genNorm_constMulMean`): the structural norm of the eddy family
  sees only the zero mode of its mean.
* `genMode_mulDrift_zero_le`: the zero mode of `drift · e` reads only the modes `±1` of `e`; with
  the drift profiles `≤ D_d` at nonzero modes and the nonzero modes of `e` scaled by `λ`
  (`genMode_drift_scale`), it is at most `D_d λ` times the structural norm of `e` at the larger
  constants. -/

open GenSem Majorant

/-! ### Explicit sums -/

/-- The sum of a list of expressions. -/
def gsumList {s : GenSort} {i : ℕ} {p : ℤ} : List (Gen s i p) → Gen s i p
  | [] => Gen.time (.const 0)
  | e :: l => Gen.add e (gsumList l)

theorem genMode_gsumList_le (D : OCData) (κ : MajConsts) (Δ : ℝ) {s : GenSort} {i : ℕ} {p : ℤ}
    (l : List (Gen s i p)) (mres : ℝ) (h : ℤ) (t : ℝ) :
    genMode D κ Δ leafNone (gsumList l) mres h t ≤
      (l.map fun e => genMode D κ Δ leafNone e mres h t).sum := by
  induction l with
  | nil =>
    simp only [gsumList, genMode, leafNone_eq, Option.elim, List.map_nil, List.sum_nil]
    split_ifs <;> simp [TimeLetter.eval]
  | cons e l ih =>
    simp only [gsumList, genMode, leafNone_eq, Option.elim, List.map_cons, List.sum_cons]
    exact add_le_add le_rfl ih

variable {Λ : Type} {V : UEnv Λ}

theorem URep.gsumList {ι : Type*} (L : List ι) (φ : ι → Λ → Vec 2 → Vec 2 → ℝ)
    (E : ι → Gen .cell V.E.i V.E.p) (h : ∀ σ ∈ L, V.URep (φ σ) (E σ)) :
    V.URep (fun l X z => (L.map fun σ => φ σ l X z).sum) (WeakGen.gsumList (L.map E)) := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact UEnv.urep_const V 0
  | cons σ L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h σ (List.mem_cons_self ..)).add (ih fun σ' hσ' => h σ' (List.mem_cons_of_mem _ hσ'))

/-! ### The means as leaves -/

/-- The family means of the level `m` as leaves, with the zero mode of their leaf-free majorant,
uniformly in time. -/
def leafMeanAt (D : OCData) (κ : MajConsts) (Δ : ℝ) (m : ℕ) :
    ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)
  | _, i, _, e@(.mean _) =>
      if i = m then some fun mres h => if h = 0 then ⨆ t, genMode D κ Δ leafNone e mres 0 t else 0
      else none
  | _, _, _, _ => none

theorem leafMeanAt_dominates (D : OCData) (κ : MajConsts) (Δ : ℝ) (m : ℕ)
    {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p) (B : ℝ → ℤ → ℝ≥0∞)
    (hB : leafMeanAt D κ Δ m e = some B) (mres : ℝ) (h : ℤ) (t : ℝ) :
    genMode D κ Δ leafNone e mres h t ≤ B mres h := by
  cases e with
  | mean w =>
    simp only [leafMeanAt] at hB
    split_ifs at hB with him
    simp only [Option.some.injEq] at hB
    subst hB
    by_cases h0 : h = 0
    · subst h0
      simp only [↓reduceIte]
      exact le_iSup (fun t' => genMode D κ Δ leafNone (Gen.mean w) mres 0 t') t
    · simp only [h0, ↓reduceIte, genMode, leafNone_eq, Option.elim, nonpos_iff_eq_zero]
  | _ => simp [leafMeanAt] at hB

theorem wsum_single_zero (a : ℝ) (L : ℕ) (f : ℤ → ℝ≥0∞) (hf : ∀ h, h ≠ 0 → f h = 0) :
    wsum a L f = f 0 := by
  unfold wsum
  rw [tsum_eq_single 0 fun h hh => by rw [hf h hh, mul_zero], modeWeight_zero, one_mul]

/-- **A constant times a mean of the level `m`**: the structural norm with the mean leaves is the
constant times the time supremum of the zero mode of the mean. -/
theorem genNorm_constMulMean (D : OCData) (κ : MajConsts) (Δ a₀ : ℝ) {m : ℕ} {p : ℤ} (c : ℝ)
    (w : Gen .cell m p) (a mres : ℝ) (t : ℝ) :
    genNorm D κ Δ a₀ (leafMeanAt D κ Δ m) (Gen.mul (Gen.time (.const c)) (Gen.mean w)) a mres 0 t =
      ENNReal.ofReal |c| * ⨆ t', genMode D κ Δ leafNone w mres 0 t' := by
  have hl : leafMeanAt D κ Δ m (Gen.mean w) = some fun mres h =>
      if h = 0 then ⨆ t, genMode D κ Δ leafNone (Gen.mean w) mres 0 t else 0 := by
    simp [leafMeanAt]
  have hm : leafMeanAt D κ Δ m (Gen.mul (Gen.time (.const c)) (Gen.mean w)) = none := rfl
  have ht : leafMeanAt D κ Δ m (Gen.time (s := .fam) (i := m) (p := p) (.const c)) = none := rfl
  simp only [genNorm, hm, ht, hl, Option.elim]
  rw [wsum_single_zero a 0 _ fun h hh => by simp [hh]]
  simp only [↓reduceIte, TimeLetter.eval]
  congr 1

/-! ### The zero mode of a drift product -/

theorem one_le_modeWeight {a : ℝ} (ha : 0 ≤ a) (L : ℕ) (h : ℤ) : 1 ≤ modeWeight a L h := by
  unfold modeWeight
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : 1 ≤ Real.exp (a * |(h : ℝ)|) := Real.one_le_exp (mul_nonneg ha (abs_nonneg _))
  have h2 : 1 ≤ (1 + |(h : ℝ)|) ^ L := one_le_pow₀ (by linarith [abs_nonneg (h : ℝ)])
  nlinarith

theorem tsum_le_wsum {a : ℝ} (ha : 0 ≤ a) (L : ℕ) (f : ℤ → ℝ≥0∞) :
    ∑' h, f h ≤ wsum a L f :=
  ENNReal.tsum_le_tsum fun h => le_mul_of_one_le_left zero_le (one_le_modeWeight ha L h)

/-- **The zero mode of a drift product reads the modes `±1`.** -/
theorem genMode_mulDrift_zero_le (D : OCData) (Δ a₀ : ℝ) (ha₀ : 0 ≤ a₀) {κ κ' : MajConsts}
    {lam Dd : ℝ≥0∞} (hl0 : lam ≠ 0) (hl1 : lam ≤ 1)
    (hd : ∀ c h, κ.drift c h ≤ lam * κ'.drift c h)
    (hg : ∀ L h, κ.geo .own L h ≤ κ'.geo .own L h) (hg0 : ∀ L h, h ≠ 0 → κ.geo .own L h = 0)
    (hCold : κ.Cold ≤ κ'.Cold) (hCslow : κ.Cslow ≤ κ'.Cslow)
    (hDd : ∀ c h, κ.drift c h ≤ if h = 0 then 0 else Dd)
    {m : ℕ} {p : ℤ} (c : Fin 2) (e : Gen .cell m p) (mres : ℝ) (t a : ℝ) (ha : 0 ≤ a) (L : ℕ) :
    genMode D κ Δ leafNone (Gen.mul (Gen.drift c) e) mres 0 t ≤
      Dd * lam * genNorm D κ' Δ a₀ leafTop e a mres L t := by
  simp only [genMode, leafNone_eq, Option.elim]
  have hterm : ∀ k : ℤ, κ.drift c k * genMode D κ Δ leafNone e mres (0 - k) t ≤
      Dd * lam * genMode D κ' Δ leafTop e mres (-k) t := by
    intro k
    by_cases hk : k = 0
    · subst hk
      have := hDd c 0
      simp only [↓reduceIte, nonpos_iff_eq_zero] at this
      rw [this, zero_mul]
      exact zero_le
    · have h1 := hDd c k
      rw [ite_eq_right hk] at h1
      have h2 : genMode D κ Δ leafNone e mres (0 - k) t ≤ lam * genMode D κ' Δ leafTop e mres (-k) t := by
        rw [zero_sub]
        exact (genMode_le_leafTop D Δ κ e mres (-k) t).trans
          ((genMode_drift_scale D Δ hl0 hl1 hd hg hg0 hCold hCslow e mres (-k) t).2 (neg_ne_zero.mpr hk))
      calc κ.drift c k * genMode D κ Δ leafNone e mres (0 - k) t
          ≤ Dd * (lam * genMode D κ' Δ leafTop e mres (-k) t) := mul_le_mul' h1 h2
        _ = _ := by ring
  calc ∑' k, κ.drift c k * genMode D κ Δ leafNone e mres (0 - k) t
      ≤ ∑' k, Dd * lam * genMode D κ' Δ leafTop e mres (-k) t := ENNReal.tsum_le_tsum hterm
    _ = Dd * lam * ∑' k, genMode D κ' Δ leafTop e mres k t := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        exact (Equiv.neg ℤ).tsum_eq fun k => genMode D κ' Δ leafTop e mres k t
    _ ≤ Dd * lam * wsum a L (fun h => genMode D κ' Δ leafTop e mres h t) :=
        mul_le_mul' le_rfl (tsum_le_wsum ha L _)
    _ ≤ _ := mul_le_mul' le_rfl (wsum_genMode_le D κ' Δ a₀ leafTop ha₀ e t a mres L ha)

end AVRegularity.Providers.WeakGen
end
