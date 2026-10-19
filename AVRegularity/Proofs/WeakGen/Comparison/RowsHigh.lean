-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Comparison.RowCoefficients
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.CycleComparison.Coarse.Fact.FBoundOps
import AVRegularity.EntryWeakAssembly.PairedForcingCostSchur

section
@[expose] public noncomputable section
section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Comparison

/-! **The descending rows of the energy bound** (`weak_comparison_descending_rows`).

At one weak passage, with the rows plan conditions, the descending solution is a coupled
solution at radius `ρ ε_i` with drift data (`weakComparison_rowDrift`, Péclet smallness above
the drift floor) and coupling constants `κ_M C_R ∑ size` (`weakComparison_edge_le`). The row
recursion (`coupledRow_recursion`) is normalized by the masses
(`weakComparison_stage_recursion`): the edge weights are the stored weights
`√(π_u/π_v) size`, whose row sums are at most one above the stored-ledger floor. It is unrolled
along stage paths of length at most `J_w R_w` (`row_recursion_unroll`). The order-zero row
energy is at most three times the normalized bound, and the normalized forcing bound is at most
sixteen times the row forcing cost. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs
  CycleJointProofs.PathReduction Construction.Preservation.Ledger

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- Scale algebra of the drift condition at radius `r ε`. -/
theorem drift_scale_le {ε r κ C α : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hC : 0 ≤ C) (hα : 0 < α) (hα1 : α < 1) (hP : ε ^ (1 + α) ≤ κ / (8192 * (C + 1))) :
    (r * ε) ^ 2 * (C * ε ^ ((1 + α) - 2) + 1) ≤ κ / 8192 := by
  have h1 : ε ^ 2 * ε ^ ((1 + α) - 2) = ε ^ (1 + α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hε]
    norm_num
  have h2 : ε ^ 2 ≤ ε ^ (1 + α) := by
    have := Real.rpow_le_rpow_of_exponent_ge hε hε1 (show 1 + α ≤ (2 : ℝ) by linarith)
    rwa [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hpos : 0 ≤ ε ^ (1 + α) := Real.rpow_nonneg hε.le _
  calc (r * ε) ^ 2 * (C * ε ^ ((1 + α) - 2) + 1)
      = r ^ 2 * (C * (ε ^ 2 * ε ^ ((1 + α) - 2)) + ε ^ 2) := by ring
    _ = r ^ 2 * (C * ε ^ (1 + α) + ε ^ 2) := by rw [h1]
    _ ≤ 1 * (C * ε ^ (1 + α) + ε ^ (1 + α)) :=
        mul_le_mul hr2 (by linarith) (by positivity) zero_le_one
    _ = (C + 1) * ε ^ (1 + α) := by ring
    _ ≤ (C + 1) * (κ / (8192 * (C + 1))) := mul_le_mul_of_nonneg_left hP (by linarith)
    _ = κ / 8192 := by field_simp

/-- **The drift data of the rows** at radius `ρ ε_i`, above the drift floor. -/
theorem weakComparison_rowDrift (c : WeakPassageInstance plan R)
    (hfloor : weakComparisonDriftFloor A ≤ c.M) (hrad : plan.radius R ≤ 1 / 2048) (i : ℕ)
    (hi : c.M < i) (t₀ t₁ : ℝ) (Kmax : ℕ) :
    TorusDriftData (c.D.κ c.M) (plan.radius R * c.D.eps i) t₀ t₁ (streamVel (c.D.Φ i)) Kmax := by
  have hΛ : 128 ≤ A.Λ := (plan.base_ge B).trans c.base_ge
  have hC0 := Construction.Preservation.Buffer.actualDriftJetConstant_nonneg
  set C := Construction.Preservation.Buffer.actualDriftJetConstant with hCdef
  have hθ : 0 < 1 / (8192 * (C + 1)) := by positivity
  unfold weakComparisonDriftFloor at hfloor
  rw [dite_eq_left hΛ] at hfloor
  have hspec := Classical.choose_spec (weak_peclet_eventually_small B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
    A.Λ hΛ (1 / (8192 * (C + 1))) hθ)
  have hP := hspec c.M hfloor (c.D.κ c.M) c.band.1 i hi
  have hε : 0 < ocEpsilon B.q A.Λ i := (Scales.epsilon_basic B.hq.1 hΛ).1
  have hε1 : ocEpsilon B.q A.Λ i ≤ 1 := (Scales.epsilon_basic B.hq.1 hΛ).2.1
  have hband := c.band.1
  have hκ : 0 < c.D.κ c.M := lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos
    (Scales.epsilon_basic (m := c.M) B.hq.1 hΛ).1 _) two_pos) hband.1
  have heps : c.D.eps i = ocEpsilon B.q A.Λ i := by
    rw [OCData.eps, c.q_eq, c.base_eq]
  have hr := plan.radius_pos R
  rw [heps]
  refine stream_torusDriftData_at B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq B.ζ B.hζ A.Λ hΛ c.D.Φ
    c.streams i (by omega) t₀ t₁ Kmax _ ?_ ?_
  · rw [le_div_iff₀ (by norm_num)]
    nlinarith
  · refine drift_scale_le hε hε1 hr.le (by linarith) hC0 B.hα₀ (by linarith [B.hα₁]) ?_
    rw [div_le_iff₀ hκ] at hP
    rw [le_div_iff₀ (by positivity)]
    calc ocEpsilon B.q A.Λ i ^ (1 + B.α) * (8192 * (C + 1))
        ≤ 1 / (8192 * (C + 1)) * c.D.κ c.M * (8192 * (C + 1)) :=
          mul_le_mul_of_nonneg_right hP (by positivity)
      _ = c.D.κ c.M := by field_simp

/-- The radius of the rows is positive and at most `ε_i`. -/
theorem weakComparison_rowRadius (c : WeakPassageInstance plan R) (i : ℕ)
    (hrad : plan.radius R ≤ 1) :
    0 < plan.radius R * c.D.eps i ∧ plan.radius R * c.D.eps i ≤ c.D.eps i := by
  have hε : 0 < c.D.eps i := Construction.Stream.ocEpsilon_pos (by
    have := (weakPassageInstance_base c).1
    omega)
  exact ⟨mul_pos (plan.radius_pos R) hε, mul_le_of_le_one_left hε.le hrad⟩

/-- The coefficient data of the rows at radius `ρ ε_i`. -/
theorem weakComparisonRowData (c : WeakPassageInstance plan R)
    (hfloor : weakComparisonCoeffFloor R ≤ c.M) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (hrad : plan.radius R ≤ 1) (a b : ℝ) :
    TorusCoefficientData (plan.radius R * c.D.eps i)
      (fun v : CompIn (c.stage i).comps => weakComparisonReserve R v.1) (1 + A.Jw * A.Nw) a b
      (weakComparisonDescendingCoeff c i) where
  radius_pos := (weakComparison_rowRadius c i hrad).1
  finite v u d := (weakComparisonDescendingCoeff_gate c hfloor i hi hit a b _
    (weakComparison_rowRadius c i hrad).1 (weakComparison_rowRadius c i hrad).2 v u d).2.2.2
  smooth t ht v u d := (weakComparisonDescendingCoeff_gate c hfloor i hi hit a b _
    (weakComparison_rowRadius c i hrad).1 (weakComparison_rowRadius c i hrad).2 v u d).2.1 t ht
  periodic t ht v u d := (weakComparisonDescendingCoeff_gate c hfloor i hi hit a b _
    (weakComparison_rowRadius c i hrad).1 (weakComparison_rowRadius c i hrad).2 v u d).2.2.1 t ht

/-- Edge sums at a row, as sums over sources and identities. -/
theorem ledger_edge_sum_target {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    {G : GenStage D ScalarH Dm bw j₀} (w : LedgerEdge G → ℝ)
    (Y : CompIn G.comps → ℝ) (v : CompIn G.comps) :
    (∑ e : LedgerEdge G, if e.1 = v then w e * Y e.2.1 else 0) =
      ∑ u, ∑ γ : G.fam.Γ v u, w ⟨v, u, γ⟩ * Y u := by
  classical
  simp [Fintype.sum_sigma]

/-- The row sums of the stored weights are at most one above the stored-ledger floor. -/
theorem weakComparison_storedRow_le (c : WeakPassageInstance plan R)
    (hstored : weakQuietStoredFloor A ≤ c.M) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (v : CompIn (c.stage i).comps) :
    ∑ u, ∑ γ : (c.stage i).fam.Γ v u,
      weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀ ⟨v, u, γ⟩ ≤ 1 := by
  classical
  have hΛ : 128 ≤ A.Λ := (plan.base_ge B).trans c.base_ge
  have htot := (exists_weak_quiet_stored_threshold A).choose_spec hΛ c.M hstored c.D c.alpha
    c.q_eq c.base_eq c.terminal c.band c.Dm c.j₀ c.P R.sX R.sZ c.stage c.construction i hi.le hit
  refine le_trans ?_ htot
  have hrow : (∑ u, ∑ γ : (c.stage i).fam.Γ v u,
      weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀ ⟨v, u, γ⟩) ≤
      ∑ v', ∑ u, ∑ γ : (c.stage i).fam.Γ v' u,
        weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀ ⟨v', u, γ⟩ :=
    Finset.single_le_sum (f := fun v' => ∑ u, ∑ γ : (c.stage i).fam.Γ v' u,
      weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀ ⟨v', u, γ⟩)
      (fun v' _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun γ _ =>
        weakStoredEdgeWeight_nonneg _ _ _ _ _) (Finset.mem_univ v)
  refine hrow.trans (le_of_eq ?_)
  simp only [weakStoredTotal, LedgerEdge, Fintype.sum_sigma]

/-- The edge constant against the stored weights. -/
theorem weakComparison_edge_le_stored (c : WeakPassageInstance plan R)
    (hfloor : weakComparisonCoeffFloor R ≤ c.M) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (a b : ℝ) (hrad : plan.radius R ≤ 1)
    (v u : CompIn (c.stage i).comps) :
    ∑ d : admissibleOrders (fun v : CompIn (c.stage i).comps => weakComparisonReserve R v.1)
        (1 + A.Jw * A.Nw) v u,
      (coefficientSeminorm (plan.radius R * c.D.eps i) (weakComparisonReserve R v.1) a b
        (weakComparisonDescendingCoeff c i v u d)).toReal *
        derivativeReserveFactor (plan.radius R * c.D.eps i) (weakComparisonReserve R v.1)
          (d.1 - 2) ≤
      c.D.κ c.M * weakComparisonEdgeConst plan R *
        Real.sqrt (weakMass c.D A.Nw A.Jw A.η₀ v.1 / weakMass c.D A.Nw A.Jw A.η₀ u.1) *
        ∑ γ : (c.stage i).fam.Γ v u, weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀ ⟨v, u, γ⟩ := by
  have hΛ1 : 1 ≤ c.D.Λ := by
    have := (weakPassageInstance_base c).1
    omega
  have hπ := fun w : CompIn (c.stage i).comps => weakMass_pos c.D A.Nw A.Jw A.η₀ A.Nw_pos
    A.Jw_pos (fun _ => Construction.Stream.ocEpsilon_pos hΛ1) w.1
  refine (weakComparison_edge_le c hfloor i hi hit a b hrad v u).trans (le_of_eq ?_)
  have hs : Real.sqrt (weakMass c.D A.Nw A.Jw A.η₀ v.1 / weakMass c.D A.Nw A.Jw A.η₀ u.1) *
      Real.sqrt (weakMass c.D A.Nw A.Jw A.η₀ u.1 / weakMass c.D A.Nw A.Jw A.η₀ v.1) = 1 := by
    rw [← Real.sqrt_mul (div_nonneg (hπ v).le (hπ u).le), div_mul_div_comm,
      mul_comm (weakMass c.D A.Nw A.Jw A.η₀ v.1), div_self (mul_pos (hπ u) (hπ v)).ne',
      Real.sqrt_one]
  rw [mul_assoc (c.D.κ c.M * weakComparisonEdgeConst plan R)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  unfold weakStoredEdgeWeight
  rw [← mul_assoc, hs, one_mul]

/-- The forcings of the descending solution at the reserves. -/
def weakRowF (hplan : WeakComparisonReservePlanOK plan) {c : WeakPassageInstance plan R}
    {r : WeakPassageRun c} {i : ℕ} (h : WeakComparisonEnergyInput r i)
    (v : CompIn (c.stage i).comps) (t : ℝ) :
    TorusHk (weakComparisonReserve R v.1) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)) :=
  truncateTorusHk ((weak_comparison_reserve_le R v.1).trans ((Nat.le_succ _).trans (hplan R)))
    (h.F v t)

/-- The sources of the descending solution at the reserves. -/
def weakRowG (hplan : WeakComparisonReservePlanOK plan) {c : WeakPassageInstance plan R}
    {r : WeakPassageRun c} {i : ℕ} (h : WeakComparisonEnergyInput r i)
    (v : CompIn (c.stage i).comps) (t : ℝ) : TorusHk (weakComparisonReserve R v.1) (ScalarH v.1.root) :=
  truncateTorusHk ((weak_comparison_reserve_le R v.1).trans ((Nat.le_succ _).trans (hplan R)))
    (h.g v t)

/-- The forcing bound of a row. -/
def weakRowΦ (hplan : WeakComparisonReservePlanOK plan) {c : WeakPassageInstance plan R}
    {r : WeakPassageRun c} {i : ℕ} (h : WeakComparisonEnergyInput r i)
    (v : CompIn (c.stage i).comps) : ℝ :=
  16 / c.D.κ c.M * (∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
      factorialNormSq (plan.radius R * c.D.eps i) (weakRowF hplan h v s).val) +
    10 * (∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
      Real.sqrt (factorialNormSq (plan.radius R * c.D.eps i) (weakRowG hplan h v s).val)) ^ 2

/-- **Normalizing by the masses and unrolling** (abstract). -/
theorem mass_recursion_unroll {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    {G : GenStage D ScalarH Dm bw j₀} (w : LedgerEdge G → ℝ) (hw : ∀ e, 0 ≤ w e)
    (π X Φ : CompIn G.comps → ℝ) (hπ : ∀ u, 0 < π u) (hX : ∀ u, 0 ≤ X u) (L : ℝ) (hL : 0 ≤ L)
    (hrec : ∀ u, X u ≤ Φ u + L * ∑ j, (∑ γ : G.fam.Γ u j, w ⟨u, j, γ⟩) * (π u / π j) * X j)
    (N : ℕ) (hN : IsEmpty (StagePath G (N + 1))) (v : CompIn G.comps) :
    X v / π v ≤ Φ v / π v +
      ∑ n ∈ Finset.range N, L ^ (n + 1) * rowPathSum w (fun u => Φ u / π u) n v := by
  have hnorm : ∀ u, X u / π u ≤ Φ u / π u +
      L * ∑ e : LedgerEdge G, if e.1 = u then w e * (X e.2.1 / π e.2.1) else 0 := by
    intro u
    rw [ledger_edge_sum_target w (fun j => X j / π j) u]
    have hsum : ∑ j, (∑ γ : G.fam.Γ u j, w ⟨u, j, γ⟩) * (π u / π j) * X j =
        π u * ∑ j, ∑ γ : G.fam.Γ u j, w ⟨u, j, γ⟩ * (X j / π j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      field_simp [(hπ j).ne']
    have hu := hrec u
    rw [hsum] at hu
    rw [div_le_iff₀ (hπ u)]
    calc X u ≤ _ := hu
      _ = _ := by field_simp [(hπ u).ne']
  exact row_recursion_unroll w hw _ _ (fun u => div_nonneg (hX u) (hπ u).le) L hL hnorm N hN v

/-- **The stage recursion of the rows.** -/
theorem weakComparison_stage_recursion (hplan : WeakComparisonReservePlanOK plan)
    (hok : WeakComparisonRowsPlanOK plan) {c : WeakPassageInstance plan R}
    {r : WeakPassageRun c} {i : ℕ} (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (h : WeakComparisonEnergyInput r i) (hf : ∀ v, weakComparisonRowForcing h v ≠ ⊤)
    (hd : WeakComparisonDescendingSolution hplan h) (hab : r.tq i ≤ r.a + A.T₀)
    (Rd : TorusCoefficientData (plan.radius R * c.D.eps i)
      (fun v : CompIn (c.stage i).comps => weakComparisonReserve R v.1) (1 + A.Jw * A.Nw)
      (r.tq i) (r.a + A.T₀) (weakComparisonDescendingCoeff c i))
    (u : CompIn (c.stage i).comps) :
    rowEnergyBound (c.D.κ c.M) (plan.radius R * c.D.eps i) (r.tq i) (r.a + A.T₀)
        (rowForcingFlux Rd (weakRowF hplan h) hd.ew) (weakRowG hplan h) u ≤
      weakRowΦ hplan h u + 32 * 1 * weakComparisonEdgeConst plan R ^ 2 *
        ∑ j, (∑ γ : (c.stage i).fam.Γ u j,
          weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀ ⟨u, j, γ⟩) *
          (weakMass c.D A.Nw A.Jw A.η₀ u.1 / weakMass c.D A.Nw A.Jw A.η₀ j.1) *
          rowEnergyBound (c.D.κ c.M) (plan.radius R * c.D.eps i) (r.tq i) (r.a + A.T₀)
            (rowForcingFlux Rd (weakRowF hplan h) hd.ew) (weakRowG hplan h) j := by
  have hcoef : weakComparisonCoeffFloor R ≤ c.M := (hok.1 R c.j₀).trans c.level_ge
  have hdrift : weakComparisonDriftFloor A ≤ c.M := (hok.2.1 R c.j₀).1.trans c.level_ge
  have hstored : weakQuietStoredFloor A ≤ c.M := (hok.2.1 R c.j₀).2.trans c.level_ge
  have hrad := hok.2.2 R
  have hrad1 : plan.radius R ≤ 1 := hrad.trans (by norm_num)
  obtain ⟨hDΛ, -, hζ, hband⟩ := weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hκ : 0 < c.D.κ c.M := by
    have := weakData_kap_pos c.D hΛ1 hζ hband c.D.term
    rwa [weakData_kap_terminal c.D c.D.term le_rfl, c.terminal] at this
  have hπ := fun w : CompIn (c.stage i).comps => weakMass_pos c.D A.Nw A.Jw A.η₀ A.Nw_pos
    A.Jw_pos (fun _ => Construction.Stream.ocEpsilon_pos hΛ1) w.1
  have hdd := weakComparison_rowDrift c hdrift hrad i hi (r.tq i) (r.a + A.T₀)
    (A.Jw * A.Rw * (A.Jw * A.Nw - 1))
  have hgate := fun v u d => weakComparisonDescendingCoeff_gate c hcoef i hi hit (r.tq i)
    (r.a + A.T₀) _ (weakComparison_rowRadius c i hrad1).1 (weakComparison_rowRadius c i hrad1).2
    v u d
  have hJN : 1 ≤ A.Jw * A.Nw := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := A.Jw_pos; omega) (by have := A.Nw_pos; omega))
  have hlp := fun v => weakComparison_forcing_lp h v (hf v)
  exact coupledRow_recursion Rd hdd hκ (by omega : 2 ≤ 1 + A.Jw * A.Nw)
    (fun v => weak_comparison_reserve_le R v.1) hab (fun v u d => (hgate v u d).1)
    (fun v => (hlp v).1.continuousLinearMap_comp _)
    (fun v => (truncateTorusHk _).integrable_comp (hlp v).2) hd.solution
    (fun w => weakMass c.D A.Nw A.Jw A.η₀ w.1) hπ (weakComparisonEdgeConst plan R) 1
    (fun v u => ∑ γ : (c.stage i).fam.Γ v u,
      weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀ ⟨v, u, γ⟩)
    (fun v u => Finset.sum_nonneg fun γ _ => weakStoredEdgeWeight_nonneg _ _ _ _ _)
    (fun v => weakComparison_storedRow_le c hstored i hi hit v)
    (fun v u => weakComparison_edge_le_stored c hcoef i hi hit (r.tq i) (r.a + A.T₀) hrad1 v u) u

/-- The row energy bounds are nonnegative. -/
theorem rowEnergyBound_nonneg {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {K : ι → ℕ} (ν r a b : ℝ) (hν : 0 < ν)
    (Q : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i)) (i : ι) : 0 ≤ rowEnergyBound ν r a b Q g i := by
  unfold rowEnergyBound
  have := integral_nonneg (μ := volume.restrict (Set.Icc a b))
    (f := fun s => factorialNormSq r (Q i s).val) fun s => factorialNormSq_nonneg r (Q i s).val
  positivity
end

/-! **Descending rows** (`weak_comparison_descending_rows`): the restated
`WeakComparisonDescendingRowsStatement` at the prices `weakComparisonRowPrices plan`
(`depth = J_w R_w`, `scalar n = 48 (32 C_R²)^n`).

The order-zero row energy is at most three times the normalized row bound
(`weakComparison_rowEnergy_le`), the normalized forcing bound is at most sixteen times the row
forcing cost (`weakComparison_rowΦ_le`), and the path kernel applied to the row forcing costs is
the unrolled sum (`weakQuietPathKernel_apply`). -/

section
open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs
  CycleJointProofs.PathReduction Construction.Preservation.Ledger

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

section Norms

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- The order-zero factorial norm at radius one is at most the full factorial norm. -/
theorem factorialNormSq_order_zero_le {K : ℕ} (ρ : ℝ) (x : TorusHk K E) :
    factorialNormSq 1 (truncateTorusHk (Nat.zero_le K) x).val ≤ factorialNormSq ρ x.val := by
  have h1 : factorialNormSq 1 (truncateTorusHk (Nat.zero_le K) x).val =
      factorialNormSq ρ (truncateTorusHk (Nat.zero_le K) x).val := by
    simp [factorialNormSq, factorialWeight]
  rw [h1]
  exact (Real.sqrt_le_sqrt_iff (factorialNormSq_nonneg ρ _)).1
    (CycleComparison.Coarse.sqrt_fNSq_torus_truncate_le ρ (Nat.zero_le K) x)

/-- The order-one gradient factorial norm at radius one is at most the full one. -/
theorem gradFactorialNormSq_order_one_le {K : ℕ} (ρ : ℝ) (y : TorusHk (K + 1) E) :
    gradFactorialNormSq 1 (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le K)) y).val ≤
      gradFactorialNormSq ρ y.val := by
  have h1 : gradFactorialNormSq 1 (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le K)) y).val =
      gradFactorialNormSq ρ (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le K)) y).val := by
    simp [gradFactorialNormSq, factorialWeight]
  rw [h1]
  exact Construction.Preservation.FullLift.gradFactorialNormSq_truncate_le (Nat.zero_le K) ρ y.val

/-- An integrable carrier trajectory has integrable factorial norm. -/
theorem integrable_sqrt_factorialNormSq_torus {K : ℕ} {μ : Measure ℝ} {g : ℝ → TorusHk K E}
    (hg : Integrable g μ) (ρ : ℝ) :
    Integrable (fun s => Real.sqrt (factorialNormSq ρ (g s).val)) μ := by
  refine (hg.norm.const_mul (Real.sqrt (factorialWeightMax ρ K))).mono'
    ((Real.continuous_sqrt.comp ((CycleComparison.Coarse.continuous_factorialNormSq ρ K).comp
      continuous_subtype_val)).comp_aestronglyMeasurable hg.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun s => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hw : 0 ≤ factorialWeightMax ρ K :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (K + 1)))
  calc Real.sqrt (factorialNormSq ρ (g s).val)
      ≤ Real.sqrt (factorialWeightMax ρ K * ‖(g s).val‖ ^ 2) :=
        Real.sqrt_le_sqrt (factorialNormSq_upper ρ (g s).val)
    _ = Real.sqrt (factorialWeightMax ρ K) * ‖g s‖ := by
        rw [Real.sqrt_mul hw, Real.sqrt_sq (norm_nonneg _)]
        rfl

end Norms

/-- Path sums are monotone in the start values. -/
theorem rowPathSum_mono {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G : GenStage D ScalarH Dm bw j₀}
    (w : LedgerEdge G → ℝ) (hw : ∀ e, 0 ≤ w e) (f f' : CompIn G.comps → ℝ)
    (hf : ∀ u, f u ≤ f' u) (n : ℕ) (v : CompIn G.comps) :
    rowPathSum w f n v ≤ rowPathSum w f' n v :=
  Finset.sum_le_sum fun π _ => by
    split
    · exact mul_le_mul_of_nonneg_left (hf _) (pathWeight_nonneg w hw π)
    · exact le_rfl

/-- **The energy of a row of the descending solution.** -/
theorem weakComparison_stage_energy (hplan : WeakComparisonReservePlanOK plan)
    (hok : WeakComparisonRowsPlanOK plan) {c : WeakPassageInstance plan R}
    {r : WeakPassageRun c} {i : ℕ} (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (h : WeakComparisonEnergyInput r i) (hf : ∀ v, weakComparisonRowForcing h v ≠ ⊤)
    (hd : WeakComparisonDescendingSolution hplan h)
    (Rd : TorusCoefficientData (plan.radius R * c.D.eps i)
      (fun v : CompIn (c.stage i).comps => weakComparisonReserve R v.1) (1 + A.Jw * A.Nw)
      (r.tq i) (r.a + A.T₀) (weakComparisonDescendingCoeff c i))
    (v : CompIn (c.stage i).comps) (t : ℝ) (ht : t ∈ Set.Icc (r.tq i) (r.a + A.T₀)) :
    factorialNormSq (plan.radius R * c.D.eps i) (hd.e v t).val + c.D.κ c.M / 2 *
        ∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
          gradFactorialNormSq (plan.radius R * c.D.eps i) (hd.ew v s).val ≤
      rowEnergyBound (c.D.κ c.M) (plan.radius R * c.D.eps i) (r.tq i) (r.a + A.T₀)
        (rowForcingFlux Rd (weakRowF hplan h) hd.ew) (weakRowG hplan h) v := by
  have hcoef : weakComparisonCoeffFloor R ≤ c.M := (hok.1 R c.j₀).trans c.level_ge
  have hdrift : weakComparisonDriftFloor A ≤ c.M := (hok.2.1 R c.j₀).1.trans c.level_ge
  have hrad := hok.2.2 R
  have hrad1 : plan.radius R ≤ 1 := hrad.trans (by norm_num)
  obtain ⟨hDΛ, -, hζ, hband⟩ := weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hκ : 0 < c.D.κ c.M := by
    have := weakData_kap_pos c.D hΛ1 hζ hband c.D.term
    rwa [weakData_kap_terminal c.D c.D.term le_rfl, c.terminal] at this
  have hdd := weakComparison_rowDrift c hdrift hrad i hi (r.tq i) (r.a + A.T₀)
    (A.Jw * A.Rw * (A.Jw * A.Nw - 1))
  have hgate := fun v u d => weakComparisonDescendingCoeff_gate c hcoef i hi hit (r.tq i)
    (r.a + A.T₀) _ (weakComparison_rowRadius c i hrad1).1 (weakComparison_rowRadius c i hrad1).2
    v u d
  have hJN : 1 ≤ A.Jw * A.Nw := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := A.Jw_pos; omega) (by have := A.Nw_pos; omega))
  have hlp := fun v => weakComparison_forcing_lp h v (hf v)
  exact coupledRow_energy Rd hdd hκ (by omega : 2 ≤ 1 + A.Jw * A.Nw)
    (fun v => weak_comparison_reserve_le R v.1) (fun v u d => (hgate v u d).1)
    (fun v => (hlp v).1.continuousLinearMap_comp _)
    (fun v => (truncateTorusHk _).integrable_comp (hlp v).2) hd.solution v t ht

/-- **The order-zero row energy** is at most three times the normalized row bound. -/
theorem weakComparison_rowEnergy_le (hplan : WeakComparisonReservePlanOK plan)
    (hok : WeakComparisonRowsPlanOK plan) {c : WeakPassageInstance plan R}
    {r : WeakPassageRun c} {i : ℕ} (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (h : WeakComparisonEnergyInput r i) (hf : ∀ v, weakComparisonRowForcing h v ≠ ⊤)
    (hd : WeakComparisonDescendingSolution hplan h) (hab : r.tq i ≤ r.a + A.T₀)
    (Rd : TorusCoefficientData (plan.radius R * c.D.eps i)
      (fun v : CompIn (c.stage i).comps => weakComparisonReserve R v.1) (1 + A.Jw * A.Nw)
      (r.tq i) (r.a + A.T₀) (weakComparisonDescendingCoeff c i))
    (v : CompIn (c.stage i).comps) :
    weakComparisonRowEnergy h v ≤ ENNReal.ofReal (3 *
      (rowEnergyBound (c.D.κ c.M) (plan.radius R * c.D.eps i) (r.tq i) (r.a + A.T₀)
        (rowForcingFlux Rd (weakRowF hplan h) hd.ew) (weakRowG hplan h) v /
        weakMass c.D A.Nw A.Jw A.η₀ v.1)) := by
  obtain ⟨hDΛ, -, hζ, hband⟩ := weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hκ : 0 < c.D.κ c.M := by
    have := weakData_kap_pos c.D hΛ1 hζ hband c.D.term
    rwa [weakData_kap_terminal c.D c.D.term le_rfl, c.terminal] at this
  have hπ := weakMass_pos c.D A.Nw A.Jw A.η₀ A.Nw_pos A.Jw_pos
    (fun _ => Construction.Stream.ocEpsilon_pos hΛ1) v.1
  set X := rowEnergyBound (c.D.κ c.M) (plan.radius R * c.D.eps i) (r.tq i) (r.a + A.T₀)
    (rowForcingFlux Rd (weakRowF hplan h) hd.ew) (weakRowG hplan h) v with hXdef
  set G := ∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
    gradFactorialNormSq (plan.radius R * c.D.eps i) (hd.ew v s).val with hGdef
  have hE := weakComparison_stage_energy hplan hok hi hit h hf hd Rd v
  have hG0 : 0 ≤ G := integral_nonneg (f := fun s =>
    gradFactorialNormSq (plan.radius R * c.D.eps i) (hd.ew v s).val)
    fun s => CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _
  have hX0 : 0 ≤ X := rowEnergyBound_nonneg _ _ _ _ hκ _ _ v
  have hκG : c.D.κ c.M * G ≤ 2 * X := by
    have := hE (r.tq i) ⟨le_rfl, hab⟩
    have h0 := factorialNormSq_nonneg (plan.radius R * c.D.eps i) (hd.e v (r.tq i)).val
    linarith
  have hsup : (⨆ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), ENNReal.ofReal (factorialNormSq 1 (h.e v t).val)) ≤
      ENNReal.ofReal X := by
    refine iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal ?_
    rw [← hd.values v t ht]
    have := hE t ht
    have hκG' : 0 ≤ c.D.κ c.M / 2 * G := mul_nonneg (by positivity) hG0
    exact (factorialNormSq_order_zero_le _ _).trans (by linarith)
  have hint : (∫⁻ t in Set.Icc (r.tq i) (r.a + A.T₀),
      ENNReal.ofReal (gradFactorialNormSq 1 (h.ew v t).val)) ≤ ENNReal.ofReal G := by
    rw [hGdef, ofReal_integral_eq_lintegral_ofReal
      (CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (hd.solution.2.1 v))
      (Filter.Eventually.of_forall fun s => CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _)]
    refine lintegral_mono_ae ?_
    filter_upwards [hd.gradients v] with t ht
    rw [← ht]
    exact ENNReal.ofReal_le_ofReal (gradFactorialNormSq_order_one_le _ _)
  unfold weakComparisonRowEnergy
  calc _ ≤ (ENNReal.ofReal (weakMass c.D A.Nw A.Jw A.η₀ v.1))⁻¹ *
        (ENNReal.ofReal X + ENNReal.ofReal (c.D.κ c.M) * ENNReal.ofReal G) := by
        gcongr
    _ = (ENNReal.ofReal (weakMass c.D A.Nw A.Jw A.η₀ v.1))⁻¹ *
        ENNReal.ofReal (X + c.D.κ c.M * G) := by
        congr 1
        rw [ENNReal.ofReal_add hX0 (mul_nonneg hκ.le hG0), ENNReal.ofReal_mul hκ.le]
    _ ≤ (ENNReal.ofReal (weakMass c.D A.Nw A.Jw A.η₀ v.1))⁻¹ * ENNReal.ofReal (3 * X) := by
        gcongr
        linarith
    _ = ENNReal.ofReal (3 * (X / weakMass c.D A.Nw A.Jw A.η₀ v.1)) := by
        rw [← mul_div_assoc, ENNReal.ofReal_div_of_pos hπ, ENNReal.div_eq_inv_mul]

/-- The row forcing cost as a real quantity. -/
theorem weakComparison_rowForcing_eq {c : WeakPassageInstance plan R} {r : WeakPassageRun c}
    {i : ℕ} (h : WeakComparisonEnergyInput r i) (hf : ∀ v, weakComparisonRowForcing h v ≠ ⊤)
    (u : CompIn (c.stage i).comps) :
    weakComparisonRowForcing h u = ENNReal.ofReal (((c.D.κ c.M)⁻¹ *
      (∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
        factorialNormSq (plan.radius R * c.D.eps i) (h.F u s).val) +
      (∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
        Real.sqrt (factorialNormSq (plan.radius R * c.D.eps i) (h.g u s).val)) ^ 2) /
      weakMass c.D A.Nw A.Jw A.η₀ u.1) := by
  obtain ⟨hDΛ, -, hζ, hband⟩ := weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hκ : 0 < c.D.κ c.M := by
    have := weakData_kap_pos c.D hΛ1 hζ hband c.D.term
    rwa [weakData_kap_terminal c.D c.D.term le_rfl, c.terminal] at this
  have hπ := weakMass_pos c.D A.Nw A.Jw A.η₀ A.Nw_pos A.Jw_pos
    (fun _ => Construction.Stream.ocEpsilon_pos hΛ1) u.1
  obtain ⟨hFm, hgi⟩ := weakComparison_forcing_lp h u (hf u)
  have hF1 := CycleComparison.Coarse.integrable_factorialNormSq_torus
    (ρ := plan.radius R * c.D.eps i) hFm
  have hg1 := integrable_sqrt_factorialNormSq_torus hgi (plan.radius R * c.D.eps i)
  have hJ₁0 := integral_nonneg (μ := volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))
    (f := fun s => factorialNormSq (plan.radius R * c.D.eps i) (h.F u s).val)
    fun s => factorialNormSq_nonneg _ _
  have hJ₂0 := integral_nonneg (μ := volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))
    (f := fun s => Real.sqrt (factorialNormSq (plan.radius R * c.D.eps i) (h.g u s).val))
    fun s => Real.sqrt_nonneg _
  unfold weakComparisonRowForcing
  rw [← ofReal_integral_eq_lintegral_ofReal hF1
      (Filter.Eventually.of_forall fun _ => factorialNormSq_nonneg _ _),
    ← ofReal_integral_eq_lintegral_ofReal hg1
      (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _),
    ← ENNReal.ofReal_inv_of_pos hκ, ← ENNReal.ofReal_mul (inv_nonneg.2 hκ.le),
    ← ENNReal.ofReal_pow hJ₂0, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_div_of_pos hπ, ENNReal.div_eq_inv_mul]

/-- The forcing bound against the full forcings. -/
theorem weakRowΦ_le (hplan : WeakComparisonReservePlanOK plan)
    {c : WeakPassageInstance plan R} {r : WeakPassageRun c} {i : ℕ}
    (h : WeakComparisonEnergyInput r i) (hf : ∀ v, weakComparisonRowForcing h v ≠ ⊤)
    (u : CompIn (c.stage i).comps) :
    weakRowΦ hplan h u ≤ 16 * ((c.D.κ c.M)⁻¹ *
      (∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
        factorialNormSq (plan.radius R * c.D.eps i) (h.F u s).val) +
      (∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
        Real.sqrt (factorialNormSq (plan.radius R * c.D.eps i) (h.g u s).val)) ^ 2) := by
  obtain ⟨hDΛ, -, hζ, hband⟩ := weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hκ : 0 < c.D.κ c.M := by
    have := weakData_kap_pos c.D hΛ1 hζ hband c.D.term
    rwa [weakData_kap_terminal c.D c.D.term le_rfl, c.terminal] at this
  obtain ⟨hFm, hgi⟩ := weakComparison_forcing_lp h u (hf u)
  set ρ := plan.radius R * c.D.eps i with hρ
  have hF1 := CycleComparison.Coarse.integrable_factorialNormSq_torus (ρ := ρ) hFm
  have hg1 := integrable_sqrt_factorialNormSq_torus hgi ρ
  have hF1' := CycleComparison.Coarse.integrable_factorialNormSq_torus (ρ := ρ)
    (hFm.continuousLinearMap_comp (truncateTorusHk ((weak_comparison_reserve_le R u.1).trans
      ((Nat.le_succ _).trans (hplan R)))))
  have hg1' := integrable_sqrt_factorialNormSq_torus ((truncateTorusHk
    ((weak_comparison_reserve_le R u.1).trans ((Nat.le_succ _).trans (hplan R)))).integrable_comp
      hgi) ρ
  have hm1 : (∫ s in Set.Icc (r.tq i) (r.a + A.T₀), factorialNormSq ρ (weakRowF hplan h u s).val)
      ≤ ∫ s in Set.Icc (r.tq i) (r.a + A.T₀), factorialNormSq ρ (h.F u s).val :=
    setIntegral_mono hF1' hF1 fun s =>
      (Real.sqrt_le_sqrt_iff (factorialNormSq_nonneg ρ _)).1
        (CycleComparison.Coarse.sqrt_fNSq_torus_truncate_le ρ _ (h.F u s))
  have hm2 : (∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
      Real.sqrt (factorialNormSq ρ (weakRowG hplan h u s).val)) ≤
      ∫ s in Set.Icc (r.tq i) (r.a + A.T₀), Real.sqrt (factorialNormSq ρ (h.g u s).val) :=
    setIntegral_mono hg1' hg1 fun s => CycleComparison.Coarse.sqrt_fNSq_torus_truncate_le ρ _ (h.g u s)
  have hm20 : 0 ≤ ∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
      Real.sqrt (factorialNormSq ρ (weakRowG hplan h u s).val) :=
    integral_nonneg (f := fun s => Real.sqrt (factorialNormSq ρ (weakRowG hplan h u s).val))
      fun s => Real.sqrt_nonneg _
  have h1 : 16 / c.D.κ c.M * (∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
      factorialNormSq ρ (weakRowF hplan h u s).val) ≤ 16 * ((c.D.κ c.M)⁻¹ *
        ∫ s in Set.Icc (r.tq i) (r.a + A.T₀), factorialNormSq ρ (h.F u s).val) := by
    rw [div_eq_mul_inv, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm1 (inv_nonneg.2 hκ.le))
      (by norm_num)
  have h2 := pow_le_pow_left₀ hm20 hm2 2
  unfold weakRowΦ
  nlinarith

/-- **The normalized forcing bound** is at most sixteen times the row forcing cost. -/
theorem weakComparison_rowΦ_le (hplan : WeakComparisonReservePlanOK plan)
    {c : WeakPassageInstance plan R} {r : WeakPassageRun c} {i : ℕ}
    (h : WeakComparisonEnergyInput r i) (hf : ∀ v, weakComparisonRowForcing h v ≠ ⊤)
    (u : CompIn (c.stage i).comps) :
    weakRowΦ hplan h u / weakMass c.D A.Nw A.Jw A.η₀ u.1 ≤
      16 * (weakComparisonRowForcing h u).toReal := by
  obtain ⟨hDΛ, -, hζ, hband⟩ := weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hκ : 0 < c.D.κ c.M := by
    have := weakData_kap_pos c.D hΛ1 hζ hband c.D.term
    rwa [weakData_kap_terminal c.D c.D.term le_rfl, c.terminal] at this
  have hπ := weakMass_pos c.D A.Nw A.Jw A.η₀ A.Nw_pos A.Jw_pos
    (fun _ => Construction.Stream.ocEpsilon_pos hΛ1) u.1
  have hJ₁0 := integral_nonneg (μ := volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))
    (f := fun s => factorialNormSq (plan.radius R * c.D.eps i) (h.F u s).val)
    fun s => factorialNormSq_nonneg _ _
  rw [weakComparison_rowForcing_eq h hf u, ENNReal.toReal_ofReal (by positivity),
    div_le_iff₀ hπ]
  refine (weakRowΦ_le hplan h hf u).trans (le_of_eq ?_)
  field_simp

/-- **The path kernel applied to row values.** -/
theorem weakQuietPathKernel_apply (prices : WeakQuietPathPrices) (c : WeakPassageInstance plan R)
    (i : ℕ) (v : CompIn (c.stage i).comps) (f : CompIn (c.stage i).comps → ℝ) :
    ∑ u, weakQuietPathKernel prices c i v u * f u = prices.scalar R 0 * f v +
      ∑ n ∈ Finset.range (prices.depth R), prices.scalar R (n + 1) *
        rowPathSum (weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀) f n v := by
  classical
  unfold weakQuietPathKernel rowPathSum
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  by_cases hv : (π.step (Fin.last n)).1 = v
  · simp only [hv, true_and, ↓reduceIte]
    rw [Finset.sum_eq_single (π.step 0).2.1]
    · simp only [↓reduceIte]
      ring
    · intro b _ hb
      simp only [Ne.symm hb, ↓reduceIte, mul_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp only [hv, false_and, ↓reduceIte, mul_zero, zero_mul, Finset.sum_const_zero]

/-- **The prices of the rows.** -/
def weakComparisonRowPrices (plan : WeakPassagePlan) : WeakQuietPathPrices where
  depth := fun {_B} {A} _R => A.Jw * A.Rw
  scalar := fun R n => 48 * (32 * 1 * weakComparisonEdgeConst plan R ^ 2) ^ n
  nonneg := fun R n => by positivity

/-- Path sums are homogeneous in the start values. -/
theorem rowPathSum_const_mul {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    {G : GenStage D ScalarH Dm bw j₀} (w : LedgerEdge G → ℝ) (a : ℝ) (f : CompIn G.comps → ℝ)
    (n : ℕ) (v : CompIn G.comps) :
    rowPathSum w (fun u => a * f u) n v = a * rowPathSum w f n v := by
  unfold rowPathSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  split <;> ring

/-- **The normalized row bound of the descending solution, unrolled**: three times the row
bound over the mass is at most the path kernel applied to the row forcing costs. -/
theorem weakComparison_rowBound_unrolled (hplan : WeakComparisonReservePlanOK plan)
    (hok : WeakComparisonRowsPlanOK plan) {c : WeakPassageInstance plan R}
    {r : WeakPassageRun c} {i : ℕ} (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (h : WeakComparisonEnergyInput r i) (hf : ∀ v, weakComparisonRowForcing h v ≠ ⊤)
    (hd : WeakComparisonDescendingSolution hplan h) (hab : r.tq i ≤ r.a + A.T₀)
    (Rd : TorusCoefficientData (plan.radius R * c.D.eps i)
      (fun v : CompIn (c.stage i).comps => weakComparisonReserve R v.1) (1 + A.Jw * A.Nw)
      (r.tq i) (r.a + A.T₀) (weakComparisonDescendingCoeff c i))
    (v : CompIn (c.stage i).comps) :
    3 * (rowEnergyBound (c.D.κ c.M) (plan.radius R * c.D.eps i) (r.tq i) (r.a + A.T₀)
        (rowForcingFlux Rd (weakRowF hplan h) hd.ew) (weakRowG hplan h) v /
        weakMass c.D A.Nw A.Jw A.η₀ v.1) ≤
      ∑ u, weakQuietPathKernel (weakComparisonRowPrices plan) c i v u *
        (weakComparisonRowForcing h u).toReal := by
  obtain ⟨hDΛ, -, hζ, hband⟩ := weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hκ : 0 < c.D.κ c.M := by
    have := weakData_kap_pos c.D hΛ1 hζ hband c.D.term
    rwa [weakData_kap_terminal c.D c.D.term le_rfl, c.terminal] at this
  have hπ := fun w : CompIn (c.stage i).comps => weakMass_pos c.D A.Nw A.Jw A.η₀ A.Nw_pos
    A.Jw_pos (fun _ => Construction.Stream.ocEpsilon_pos hΛ1) w.1
  set L := 32 * 1 * weakComparisonEdgeConst plan R ^ 2 with hL
  have hL0 : 0 ≤ L := by positivity
  set F := fun u => (weakComparisonRowForcing h u).toReal with hFdef
  have hN : IsEmpty (StagePath (c.stage i) (A.Jw * A.Rw + 1)) :=
    ⟨fun π => absurd (weakConstruction_path_length_bound c.P _ c.M A.Jw 0 _ c.stage
      c.construction i hi.le hit _ π) (by simp)⟩
  have hB := mass_recursion_unroll (weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀)
    (weakStoredEdgeWeight_nonneg _ _ _ _) (fun w => weakMass c.D A.Nw A.Jw A.η₀ w.1) _
    (weakRowΦ hplan h) hπ (fun u => rowEnergyBound_nonneg _ _ _ _ hκ _ _ u) L hL0
    (weakComparison_stage_recursion hplan hok hi hit h hf hd hab Rd) _ hN v
  have hΦF : ∀ u, weakRowΦ hplan h u / weakMass c.D A.Nw A.Jw A.η₀ u.1 ≤ 16 * F u :=
    weakComparison_rowΦ_le hplan h hf
  rw [weakQuietPathKernel_apply]
  have hpath : ∀ n, rowPathSum (weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀)
      (fun u => weakRowΦ hplan h u / weakMass c.D A.Nw A.Jw A.η₀ u.1) n v ≤
      16 * rowPathSum (weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀) F n v := fun n =>
    (rowPathSum_mono _ (weakStoredEdgeWeight_nonneg _ _ _ _) _ _ hΦF n v).trans
      (le_of_eq (rowPathSum_const_mul _ 16 F n v))
  have hsum : ∑ n ∈ Finset.range (A.Jw * A.Rw), L ^ (n + 1) *
        rowPathSum (weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀)
          (fun u => weakRowΦ hplan h u / weakMass c.D A.Nw A.Jw A.η₀ u.1) n v ≤
      ∑ n ∈ Finset.range (A.Jw * A.Rw), L ^ (n + 1) *
        (16 * rowPathSum (weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀) F n v) :=
    Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hpath n) (pow_nonneg hL0 _)
  have hfin : 3 * ∑ n ∈ Finset.range (A.Jw * A.Rw), L ^ (n + 1) *
        (16 * rowPathSum (weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀) F n v) =
      ∑ n ∈ Finset.range ((weakComparisonRowPrices plan).depth R),
        (weakComparisonRowPrices plan).scalar R (n + 1) *
          rowPathSum (weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀) F n v := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [weakComparisonRowPrices, hL]
    ring
  have h0 : (weakComparisonRowPrices plan).scalar R 0 = 48 := by
    simp [weakComparisonRowPrices]
  rw [h0, ← hfin]
  have hB' : rowEnergyBound (c.D.κ c.M) (plan.radius R * c.D.eps i) (r.tq i) (r.a + A.T₀)
        (rowForcingFlux Rd (weakRowF hplan h) hd.ew) (weakRowG hplan h) v /
        weakMass c.D A.Nw A.Jw A.η₀ v.1 ≤
      weakRowΦ hplan h v / weakMass c.D A.Nw A.Jw A.η₀ v.1 +
        ∑ n ∈ Finset.range (A.Jw * A.Rw), L ^ (n + 1) *
          rowPathSum (weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀)
            (fun u => weakRowΦ hplan h u / weakMass c.D A.Nw A.Jw A.η₀ u.1) n v := hB
  have hv := hΦF v
  linarith


/-- **The unrolled bound of a row in the forcing costs.** -/
theorem weakComparison_row_real_bound (hplan : WeakComparisonReservePlanOK plan)
    (hok : WeakComparisonRowsPlanOK plan) {c : WeakPassageInstance plan R}
    {r : WeakPassageRun c} {i : ℕ} (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (h : WeakComparisonEnergyInput r i) (hf : ∀ v, weakComparisonRowForcing h v ≠ ⊤)
    (hd : WeakComparisonDescendingSolution hplan h) (hab : r.tq i ≤ r.a + A.T₀)
    (v : CompIn (c.stage i).comps) :
    weakComparisonRowEnergy h v ≤ ENNReal.ofReal
      (∑ u, weakQuietPathKernel (weakComparisonRowPrices plan) c i v u *
        (weakComparisonRowForcing h u).toReal) := by
  have hcoef : weakComparisonCoeffFloor R ≤ c.M := (hok.1 R c.j₀).trans c.level_ge
  have hrad1 : plan.radius R ≤ 1 := (hok.2.2 R).trans (by norm_num)
  have Rd := weakComparisonRowData c hcoef i hi hit hrad1 (r.tq i) (r.a + A.T₀)
  exact (weakComparison_rowEnergy_le hplan hok hi hit h hf hd hab Rd v).trans
    (ENNReal.ofReal_le_ofReal (weakComparison_rowBound_unrolled hplan hok hi hit h hf hd hab Rd v))

/-- **Descending rows** (`WeakComparisonDescendingRowsStatement` at the row prices). -/
theorem weak_comparison_descending_rows (plan : WeakPassagePlan)
    (hplan : WeakComparisonReservePlanOK plan) :
    WeakComparisonDescendingRowsStatement plan hplan (weakComparisonRowPrices plan) := by
  intro hok B A R c r i hi hit h hf hd v
  by_cases hab : r.tq i ≤ r.a + A.T₀
  · refine (weakComparison_row_real_bound hplan hok hi hit h hf hd hab v).trans (le_of_eq ?_)
    obtain ⟨hK, -, -, -⟩ := weak_quiet_path_schur plan (weakComparisonRowPrices plan) c i
    rw [ENNReal.ofReal_sum_of_nonneg fun u _ =>
      mul_nonneg (hK v u) ENNReal.toReal_nonneg]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [ENNReal.ofReal_mul (hK v u), ENNReal.ofReal_toReal (hf u)]
  · have hI : Set.Icc (r.tq i) (r.a + A.T₀) = ∅ := Set.Icc_eq_empty hab
    have hz : weakComparisonRowEnergy h v = 0 := by
      unfold weakComparisonRowEnergy
      simp [hI]
    rw [hz]
    exact bot_le
end

end AVRegularity.Providers.WeakGen.Comparison
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Comparison

/-! **The bootstrap of the comparison energy** (`weak_comparison_bootstrap`). At one weak
passage, the order-zero
solution of the unregularized system (`WeakComparisonEnergyInput`) is the order-zero truncation
of a coupled solution at the descending reserves, at every time of the window, with its
gradients almost everywhere.

The coupled solution exists by `coupled_energy_torus` at rank-scaled masses
(`triangular_coupled_exists`): the coefficients lower the component rank, they are regular above
the coefficient floor (`weakComparisonDescendingCoeff_gate`), the drift is the actual stream
velocity at a small radius (`stream_torusDriftData`), and the forcings are integrable in time
(`weakComparison_forcing_lp`). The identification is `kernel_solution_identified`: the kernels
have width zero (`sysS_isoPairedKernel_zero`) and the physical coefficients vanish at the
non-admissible orders. -/

open WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- Every edge of a passage stage lowers the component rank. -/
theorem weakComparison_edge_rank (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v u : CompIn (c.stage i).comps) (hγ : Nonempty ((c.stage i).fam.Γ v u)) :
    weakComponentRank u.1 < weakComponentRank v.1 :=
  (weakConstruction_rank_bounds c.P _ c.M A.Jw 0 _ c.stage c.construction i hi.le hit).2 v u
    hγ.some

/-- The descending coefficients vanish unless they lower the rank. -/
theorem weakComparisonDescendingCoeff_triangular (c : WeakPassageInstance plan R) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v u : CompIn (c.stage i).comps)
    (hvu : ¬ weakComponentRank u.1 < weakComponentRank v.1)
    (d : admissibleOrders (fun v : CompIn (c.stage i).comps => weakComparisonReserve R v.1)
      (1 + A.Jw * A.Nw) v u) :
    weakComparisonDescendingCoeff c i v u d = 0 := by
  funext t x
  exact Finset.sum_eq_zero fun γ _ => absurd (weakComparison_edge_rank c i hi hit v u ⟨γ⟩) hvu

/-- The physical coefficients vanish at the non-admissible orders of the descending reserves. -/
theorem weakComparison_physCoeff_nonadmissible (c : WeakPassageInstance plan R) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v u : CompIn (c.stage i).comps)
    (γ : (c.stage i).fam.Γ v u) (n : ℕ) (hn : n ∈ Finset.Icc 2 c.Dm)
    (hna : n ∉ admissibleOrders (fun v : CompIn (c.stage i).comps => weakComparisonReserve R v.1)
      (1 + A.Jw * A.Nw) v u) (s : ℝ) (x : Vec 2) :
    (c.stage i).physCoeff v u γ n s x = 0 := by
  by_cases hle : n ≤ 1 + A.Jw * A.Nw
  · exact absurd (weak_comparison_edge_admissible c i hi hit v u γ n (Finset.mem_Icc.1 hn).1 hle)
      hna
  · exact congrFun (congrFun (weak_comparison_physCoeff_zero_above c i hi hit v u γ n
      (not_le.mp hle)) s) x

/-- On an empty window the zero fields are a descending solution. -/
theorem weakComparison_descending_empty (hplan : WeakComparisonReservePlanOK plan)
    {c : WeakPassageInstance plan R} {r : WeakPassageRun c} {i : ℕ}
    (h : WeakComparisonEnergyInput r i) (hab : ¬ r.tq i ≤ r.a + A.T₀) :
    Nonempty (WeakComparisonDescendingSolution hplan h) := by
  have hI : Set.Icc (r.tq i) (r.a + A.T₀) = ∅ := Set.Icc_eq_empty hab
  refine ⟨⟨fun _ _ => 0, fun _ _ => 0, fun _ t ht => absurd (hI ▸ ht) (Set.notMem_empty t),
    fun _ => ae_restrict_of_forall_mem measurableSet_Icc fun t ht =>
      absurd (hI ▸ ht) (Set.notMem_empty t), ?_⟩⟩
  refine ⟨fun _ => hI ▸ continuousOn_empty _, fun _ => torusHk_memLp_zero _ _,
    fun _ => Filter.Eventually.of_forall fun _ => map_zero _, fun _ => rfl, ?_⟩
  intro _ t ht
  exact absurd (hI ▸ ht) (Set.notMem_empty t)

/-- **The bootstrap on a nonempty window.** -/
theorem weakComparison_descending_main (hplan : WeakComparisonReservePlanOK plan)
    (hcoeff : WeakComparisonCoeffPlanOK plan) {c : WeakPassageInstance plan R}
    {r : WeakPassageRun c} {i : ℕ} (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (h : WeakComparisonEnergyInput r i) (hf : ∀ v, weakComparisonRowForcing h v ≠ ⊤)
    (hab : r.tq i ≤ r.a + A.T₀) :
    Nonempty (WeakComparisonDescendingSolution hplan h) := by
  have hfloor : weakComparisonCoeffFloor R ≤ c.M := (hcoeff R c.j₀).trans c.level_ge
  obtain ⟨hDΛ, -, hζ, hband⟩ := weakPassageInstance_base c
  have hκ : 0 < c.D.κ c.M := by
    have := weakData_kap_pos c.D (by omega) hζ hband c.D.term
    rwa [weakData_kap_terminal c.D c.D.term le_rfl, c.terminal] at this
  obtain ⟨ρ₀, hρ₀, hdrift⟩ := stream_torusDriftData B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq
    B.ζ B.hζ A.Λ ((plan.base_ge B).trans c.base_ge) c.D.Φ c.streams i (by omega) hκ (r.tq i)
    (r.a + A.T₀) (A.Jw * A.Rw * (A.Jw * A.Nw - 1))
  have hρ : 0 < min ρ₀ (c.D.eps i) := lt_min hρ₀ (Construction.Stream.ocEpsilon_pos (by omega))
  have hd := hdrift _ hρ (min_le_left _ _)
  have hJN : 1 ≤ A.Jw * A.Nw := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := A.Jw_pos; omega) (by have := A.Nw_pos; omega))
  have hgate := weakComparisonDescendingCoeff_gate c hfloor i hi hit (r.tq i) (r.a + A.T₀) _ hρ
    (min_le_right _ _)
  have hlp := fun v => weakComparison_forcing_lp h v (hf v)
  obtain ⟨u', w', hc⟩ := triangular_coupled_exists hd hab hρ hκ (by omega : 2 ≤ 1 + A.Jw * A.Nw)
    (fun v : CompIn (c.stage i).comps => weakComparisonReserve R v.1)
    (fun v => weak_comparison_reserve_le R v.1) (weakComparisonDescendingCoeff c i)
    (fun v u d => (hgate v u d).1) (fun v u d => (hgate v u d).2.1)
    (fun v u d => (hgate v u d).2.2.1) (fun v u d => (hgate v u d).2.2.2)
    (fun v => weakComponentRank v.1) (weakComparisonDescendingCoeff_triangular c i hi hit)
    (fun v t => truncateTorusHk ((weak_comparison_reserve_le R v.1).trans
      ((Nat.le_succ _).trans (hplan R))) (h.F v t))
    (fun v => (hlp v).1.continuousLinearMap_comp _)
    (fun v t => truncateTorusHk ((weak_comparison_reserve_le R v.1).trans
      ((Nat.le_succ _).trans (hplan R))) (h.g v t))
    (fun v => (truncateTorusHk _).integrable_comp (hlp v).2)
  have hsol := h.solution
  unfold WeakErrSol at hsol
  have hid := kernel_solution_identified (P := fun v u γ n => (c.stage i).physCoeff v u γ n)
    hd hab hρ hκ le_rfl (by omega) (fun _ _ _ _ _ => rfl)
    (fun v u γ n hn hna s x => weakComparison_physCoeff_nonadmissible c i hi hit v u γ n
      (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hn).1, (Finset.mem_Icc.1 hn).2.trans c.order_ge⟩)
      hna s x) (fun v => weakComponentRank v.1)
    (weakComparison_edge_rank c i hi hit)
    (fun v u γ s => sysS_isoPairedKernel_zero c.P R.nW A.hφ₀ A.mass (c.stage i) v u γ s)
    hsol hc (fun _ => map_zero _) (fun _ _ => rfl) (fun _ _ => rfl)
  exact ⟨⟨u', w', fun v t ht => hid v t ht,
    fun v => lift_identified (hid v) (hc.2.2.1 v) (hsol.2.2.1 v), hc⟩⟩

/-- **The bootstrap of the comparison energy** (`WeakComparisonBootstrapStatement`). -/
theorem weak_comparison_bootstrap (plan : WeakPassagePlan)
    (hplan : WeakComparisonReservePlanOK plan) : WeakComparisonBootstrapStatement plan hplan := by
  intro hcoeff B A R c r i hi hit h hf
  by_cases hab : r.tq i ≤ r.a + A.T₀
  · exact weakComparison_descending_main hplan hcoeff hi hit h hf hab
  · exact weakComparison_descending_empty hplan h hab

end AVRegularity.Providers.WeakGen.Comparison
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Comparison

/-! **The path price and the zero-data energy bound.**

* `weak_comparison_path_price`: at the row prices, the path cost is at most
  `48 ∑_{n ≤ J_w R_w} (32 C_R²)^n` (the stored totals are at most one above the stored floor),
  hence at most `energyC²` under `WeakComparisonEnergyPlanOK`.
* `weak_comparison_energy`: the zero-data energy bound (`WeakComparisonEnergyStatement`) for every passage plan with
  the reserve, rows and energy plan conditions and positive energy constant: the bootstrap, the
  descending rows and the path price assembled by `weak_comparison_energy_of_descending_ingredients`.
* `weakComparisonPassagePlan`: a refinement of any passage plan satisfying all of these
  (`weakComparisonPassagePlan_ok`). `weak_passage_comparison_of_residual` and its form at
  `(1, 400)` then leave only the residual on the refined plan. -/

open WeakEntryProofs WeakEntryProofs.Assembly

/-- The total row price of a request. -/
def weakComparisonRowPriceTotal (plan : WeakPassagePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) : ℝ :=
  48 * ∑ n ∈ Finset.range (A.Jw * A.Rw + 1), (32 * 1 * weakComparisonEdgeConst plan R ^ 2) ^ n

/-- Plan condition of the path price: the energy constant dominates the total row price. -/
def WeakComparisonEnergyPlanOK (plan : WeakPassagePlan) : Prop :=
  ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    weakComparisonRowPriceTotal plan R ≤ plan.energyC R ^ 2

/-- **The path price** at the row prices. -/
theorem weak_comparison_path_price (plan : WeakPassagePlan)
    (hE : WeakComparisonEnergyPlanOK plan) :
    WeakComparisonPathPriceStatement plan (weakComparisonRowPrices plan) := by
  intro hstored B A R c i hi hit
  have hΛ : 128 ≤ A.Λ := (plan.base_ge B).trans c.base_ge
  set T := weakStoredTotal (c.stage i) A.Nw A.Jw A.η₀ with hT
  have hT1 : T ≤ 1 := (exists_weak_quiet_stored_threshold A).choose_spec hΛ c.M
    ((hstored R c.j₀).trans c.level_ge) c.D c.alpha c.q_eq c.base_eq c.terminal c.band c.Dm
    c.j₀ c.P R.sX R.sZ c.stage c.construction i hi.le hit
  have hT0 : 0 ≤ T := weakStoredTotal_nonneg _ _ _ _
  set L := 32 * 1 * weakComparisonEdgeConst plan R ^ 2 with hL
  have hL0 : 0 ≤ L := by positivity
  refine le_trans ?_ (hE R)
  unfold weakQuietPathCost weakComparisonRowPriceTotal
  simp only [weakComparisonRowPrices]
  rw [Finset.sum_range_succ', pow_zero, mul_add, Finset.mul_sum, mul_one, add_comm (48 : ℝ)]
  refine add_le_add (Finset.sum_le_sum fun n _ => ?_) le_rfl
  rw [← hL]
  have hp : T ^ (n + 1) ≤ 1 := pow_le_one₀ hT0 hT1
  have hq : 0 ≤ 48 * L ^ (n + 1) := by positivity
  calc 48 * L ^ (n + 1) * T ^ (n + 1) ≤ 48 * L ^ (n + 1) * 1 :=
        mul_le_mul_of_nonneg_left hp hq
    _ = 48 * L ^ (n + 1) := mul_one _

/-- **The zero-data energy bound**: zero-data energy for an actual weak stage, for every passage plan with the reserve,
rows and energy plan conditions and positive energy constant. -/
theorem weak_comparison_energy (plan : WeakPassagePlan) (hplan : WeakComparisonReservePlanOK plan)
    (hpositive : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      0 < plan.energyC R)
    (hrows : WeakComparisonRowsPlanOK plan) (hE : WeakComparisonEnergyPlanOK plan) :
    WeakComparisonEnergyStatement plan :=
  weak_comparison_energy_of_descending_ingredients plan hplan (weakComparisonRowPrices plan)
    hpositive hrows (weak_comparison_bootstrap plan hplan)
    (weak_comparison_descending_rows plan hplan) (weak_comparison_path_price plan hE)

/-! ### The passage plan refinement and the comparison from its residual -/

/-- The energy refinement of a passage plan, before the energy constant: the radius shrinks to
`1/2048`, the forcing order covers the reserves, the level floor covers the coefficient, drift
and stored floors. -/
def weakComparisonPassagePlan₁ (plan : WeakPassagePlan) : WeakPassagePlan :=
  { plan with
    radius := fun R => min (plan.radius R) (1 / 2048)
    radius_pos := fun R => lt_min (plan.radius_pos R) (by norm_num)
    forcingOrder := fun {_B} {A} R => max (plan.forcingOrder R)
      (A.Jw * A.Rw * (A.Jw * A.Nw - 1) + 1)
    levelFloor := fun {_B} {A} R j₀ => max (plan.levelFloor R j₀)
      (max (weakComparisonCoeffFloor R) (max (weakComparisonDriftFloor A) (weakQuietStoredFloor A))) }

/-- **The energy refinement of a passage plan**: the energy constant dominates the row price. -/
def weakComparisonPassagePlan (plan : WeakPassagePlan) : WeakPassagePlan :=
  { weakComparisonPassagePlan₁ plan with
    energyC := fun R => max 1 (Real.sqrt (weakComparisonRowPriceTotal (weakComparisonPassagePlan₁ plan) R))
    energyC_nonneg := fun _R => zero_le_one.trans (le_max_left _ _) }

/-- The refinement satisfies every plan condition of the energy bound. -/
theorem weakComparisonPassagePlan_ok (plan : WeakPassagePlan) :
    WeakComparisonReservePlanOK (weakComparisonPassagePlan plan) ∧
    (∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      0 < (weakComparisonPassagePlan plan).energyC R) ∧
    WeakComparisonRowsPlanOK (weakComparisonPassagePlan plan) ∧
    WeakComparisonEnergyPlanOK (weakComparisonPassagePlan plan) := by
  refine ⟨fun R => le_max_right _ _, fun R => zero_lt_one.trans_le (le_max_left _ _),
    ⟨fun R j₀ => (le_max_left _ _).trans (le_max_right _ _),
      fun R j₀ => ⟨((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _),
        ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)⟩,
      fun R => min_le_right _ _⟩, fun {B} {A} R => ?_⟩
  have hT : 0 ≤ weakComparisonRowPriceTotal (weakComparisonPassagePlan₁ plan) R := by
    unfold weakComparisonRowPriceTotal
    positivity
  change weakComparisonRowPriceTotal (weakComparisonPassagePlan₁ plan) R ≤
    (max 1 (Real.sqrt (weakComparisonRowPriceTotal (weakComparisonPassagePlan₁ plan) R))) ^ 2
  calc weakComparisonRowPriceTotal (weakComparisonPassagePlan₁ plan) R
      = Real.sqrt (weakComparisonRowPriceTotal (weakComparisonPassagePlan₁ plan) R) ^ 2 :=
        (Real.sq_sqrt hT).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2

/-- **The energy bound on the refined passage plan.** -/
theorem weak_comparison_energy_passage (plan : WeakPassagePlan) :
    WeakComparisonEnergyStatement (weakComparisonPassagePlan plan) := by
  obtain ⟨hplan, hpos, hrows, hE⟩ := weakComparisonPassagePlan_ok plan
  exact weak_comparison_energy _ hplan hpos hrows hE

/-- **The weak passage comparison at `(1, 400)` from its residual** on the refined plan. -/
theorem weak_passage_comparison_at_of_residual (plan : WeakPassagePlan)
    (hres : WeakComparisonResidualStatement (weakComparisonPassagePlan plan)) :
    WeakPassageComparisonAt 1 400 :=
  weak_passage_comparison_at_of_ingredients _ hres (weak_comparison_energy_passage plan)

/-- **The weak passage comparison from its residual** on the refined plan. -/
theorem weak_passage_comparison_of_residual (plan : WeakPassagePlan)
    (hres : WeakComparisonResidualStatement (weakComparisonPassagePlan plan)) :
    WeakPassageComparisonStatement :=
  weak_passage_comparison_of_ingredients _ hres (weak_comparison_energy_passage plan)

end AVRegularity.Providers.WeakGen.Comparison
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Comparison

/-! **The row energy at the component reserves** (for the weak identity).

The comparison bounds the error of a weak passage at the order zero. The weak identity
applies the readout of the level `i` to that error, which differentiates it
`(M + J_w − i)·N_w` times. The proof of the comparison already holds the error at a positive order: the
descending solution `WeakComparisonDescendingSolution` is a representative of the error at the
reserves `weakComparisonReserve R v = (J_wR_w − rank v)(J_wN_w − 1)`, and its row energy is taken
at the radius `c·ε_i` (`weakComparison_stage_energy`). This module keeps that order.

* `weakComparison_row_high_bound`: for the descending solution, at every time of the window,
  `π_v⁻¹ |e_v(t)|²_{cε_i} ≤ ∑_u K(v, u) · (row forcing cost of u)`, with the path kernel of the
  order-zero row estimate.
* `weak_comparison_high_energy` (`WeakComparisonHighEnergyStatement`): there is a descending
  solution with `∑_v π_v⁻¹ |e_v(t)|²_{cε_i} ≤ energyC² · ∑_u (row forcing cost of u)` on the
  window. The right side is the square of the bound of the comparison.

* `weak_passage_comparison_high_of_residual` (`WeakPassageComparisonHighStatement`): with the
  residual (through `WeakComparisonResidualStatement`), the error of a comparison input
  has a representative at the reserves with mass norm `≤ energyC · forceC · ε_M^{P_1} · Φ` at
  `c·ε_i`. This is what the weak identity reads.

A component of the stage `i` has rank at most `(M + J_w − i)·R_w`
(`weakConstruction_rank_bounds`), so its reserve is at least `(i − M)·R_w·(J_wN_w − 1)`. For
`R_w ≥ 1` and `N_w ≥ 6` this is at least `(M + J_w − i)·N_w + 5`, the order that the readout of
the level `i` needs.

The degenerate cases are included:
- Zero forcing: every row cost is `0`, so the descending solution is `0` on the window.
- A stage with one component and no edge (the root, `i = M + J_w`): the kernel is its diagonal
  price `48`, and the bound is the scalar forced energy at the reserve `J_wR_w(J_wN_w − 1)`.
- `R_w = 0`: every reserve is `0` and the statement is the order-zero row estimate.
- Constants: `energyC` and the kernel do not read `D_m`. -/

open WeakEntryProofs WeakEntryProofs.Assembly EntryWeakProofs CycleJointProofs
  CycleJointProofs.PathReduction Construction.Preservation.Ledger

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **A row of the descending solution at its reserve**, at every time of the window. -/
theorem weakComparison_row_high_bound (hplan : WeakComparisonReservePlanOK plan)
    (hok : WeakComparisonRowsPlanOK plan) {c : WeakPassageInstance plan R}
    {r : WeakPassageRun c} {i : ℕ} (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (h : WeakComparisonEnergyInput r i) (hf : ∀ v, weakComparisonRowForcing h v ≠ ⊤)
    (hd : WeakComparisonDescendingSolution hplan h)
    (v : CompIn (c.stage i).comps) (t : ℝ) (ht : t ∈ Set.Icc (r.tq i) (r.a + A.T₀)) :
    (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
        factorialNormSq (plan.radius R * c.D.eps i) (hd.e v t).val ≤
      ∑ u, weakQuietPathKernel (weakComparisonRowPrices plan) c i v u *
        (weakComparisonRowForcing h u).toReal := by
  have hab : r.tq i ≤ r.a + A.T₀ := ht.1.trans ht.2
  have hcoef : weakComparisonCoeffFloor R ≤ c.M := (hok.1 R c.j₀).trans c.level_ge
  have hrad1 : plan.radius R ≤ 1 := (hok.2.2 R).trans (by norm_num)
  have Rd := weakComparisonRowData c hcoef i hi hit hrad1 (r.tq i) (r.a + A.T₀)
  obtain ⟨hDΛ, -, hζ, hband⟩ := weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hκ : 0 < c.D.κ c.M := by
    have := weakData_kap_pos c.D hΛ1 hζ hband c.D.term
    rwa [weakData_kap_terminal c.D c.D.term le_rfl, c.terminal] at this
  have hπ := weakMass_pos c.D A.Nw A.Jw A.η₀ A.Nw_pos A.Jw_pos
    (fun _ => Construction.Stream.ocEpsilon_pos hΛ1) v.1
  have hE := weakComparison_stage_energy hplan hok hi hit h hf hd Rd v t ht
  have h3 := weakComparison_rowBound_unrolled hplan hok hi hit h hf hd hab Rd v
  have hG0 : 0 ≤ ∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
      gradFactorialNormSq (plan.radius R * c.D.eps i) (hd.ew v s).val :=
    integral_nonneg (f := fun s =>
      gradFactorialNormSq (plan.radius R * c.D.eps i) (hd.ew v s).val)
      fun s => CycleComparison.Coarse.gradFactorialNormSq_nonneg _ _
  have hX0 : 0 ≤ rowEnergyBound (c.D.κ c.M) (plan.radius R * c.D.eps i) (r.tq i) (r.a + A.T₀)
      (rowForcingFlux Rd (weakRowF hplan h) hd.ew) (weakRowG hplan h) v :=
    rowEnergyBound_nonneg _ _ _ _ hκ _ _ v
  have hκG : 0 ≤ c.D.κ c.M / 2 * ∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
      gradFactorialNormSq (plan.radius R * c.D.eps i) (hd.ew v s).val :=
    mul_nonneg (by positivity) hG0
  have h1 : factorialNormSq (plan.radius R * c.D.eps i) (hd.e v t).val ≤
      rowEnergyBound (c.D.κ c.M) (plan.radius R * c.D.eps i) (r.tq i) (r.a + A.T₀)
        (rowForcingFlux Rd (weakRowF hplan h) hd.ew) (weakRowG hplan h) v := by linarith
  have h2 := div_nonneg hX0 hπ.le
  calc (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
        factorialNormSq (plan.radius R * c.D.eps i) (hd.e v t).val
      ≤ (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
        rowEnergyBound (c.D.κ c.M) (plan.radius R * c.D.eps i) (r.tq i) (r.a + A.T₀)
          (rowForcingFlux Rd (weakRowF hplan h) hd.ew) (weakRowG hplan h) v :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hπ.le)
    _ = rowEnergyBound (c.D.κ c.M) (plan.radius R * c.D.eps i) (r.tq i) (r.a + A.T₀)
          (rowForcingFlux Rd (weakRowF hplan h) hd.ew) (weakRowG hplan h) v /
          weakMass c.D A.Nw A.Jw A.η₀ v.1 := inv_mul_eq_div _ _
    _ ≤ 3 * (rowEnergyBound (c.D.κ c.M) (plan.radius R * c.D.eps i) (r.tq i) (r.a + A.T₀)
          (rowForcingFlux Rd (weakRowF hplan h) hd.ew) (weakRowG hplan h) v /
          weakMass c.D A.Nw A.Jw A.η₀ v.1) := by linarith
    _ ≤ _ := h3

/-- **The energy bound at the component reserves**: the error of a weak comparison with finite row forcing costs
has a representative at the reserves `weakComparisonReserve R v` (a descending solution) whose
mass norm at the radius `c·ε_i` is bounded, at every time of the window, by `energyC²` times the
sum of the row forcing costs. -/
def WeakComparisonHighEnergyStatement (plan : WeakPassagePlan)
    (hplan : WeakComparisonReservePlanOK plan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → ∀ h : WeakComparisonEnergyInput r i,
    (∀ v, weakComparisonRowForcing h v ≠ ⊤) →
    ∃ hd : WeakComparisonDescendingSolution hplan h,
      ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
        ∑ v, (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
            factorialNormSq (plan.radius R * c.D.eps i) (hd.e v t).val ≤
          plan.energyC R ^ 2 * ∑ u, (weakComparisonRowForcing h u).toReal

/-- **The energy bound at the component reserves**, for every passage plan with the reserve, rows and energy
plan conditions. -/
theorem weak_comparison_high_energy (plan : WeakPassagePlan)
    (hplan : WeakComparisonReservePlanOK plan) (hrows : WeakComparisonRowsPlanOK plan)
    (hE : WeakComparisonEnergyPlanOK plan) : WeakComparisonHighEnergyStatement plan hplan := by
  intro B A R c r i hi hit h hf
  obtain ⟨hd⟩ := weak_comparison_bootstrap plan hplan hrows.1 c r i hi hit h hf
  refine ⟨hd, fun t ht => ?_⟩
  obtain ⟨hK, -, -, hcol⟩ := weak_quiet_path_schur plan (weakComparisonRowPrices plan) c i
  have hb := weak_comparison_path_price plan hE (fun R j₀ => (hrows.2.1 R j₀).2) c i hi hit
  calc ∑ v, (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
          factorialNormSq (plan.radius R * c.D.eps i) (hd.e v t).val
      ≤ ∑ v, ∑ u, weakQuietPathKernel (weakComparisonRowPrices plan) c i v u *
          (weakComparisonRowForcing h u).toReal :=
        Finset.sum_le_sum fun v _ => weakComparison_row_high_bound hplan hrows hi hit h hf hd v t ht
    _ = ∑ u, (∑ v, weakQuietPathKernel (weakComparisonRowPrices plan) c i v u) *
          (weakComparisonRowForcing h u).toReal := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ => (Finset.sum_mul _ _ _).symm
    _ ≤ ∑ u, plan.energyC R ^ 2 * (weakComparisonRowForcing h u).toReal :=
        Finset.sum_le_sum fun u _ =>
          mul_le_mul_of_nonneg_right ((hcol u).trans hb) ENNReal.toReal_nonneg
    _ = plan.energyC R ^ 2 * ∑ u, (weakComparisonRowForcing h u).toReal :=
        (Finset.mul_sum _ _ _).symm

/-- **The weak passage comparison at the component reserves**: the error `h.e` of a comparison
input has a representative at the reserves `weakComparisonReserve R v`, equal to it after
truncation on the window, whose mass norm at the radius `c·ε_i` is at most
`energyC · forceC · ε_M^{P_w + 2q^{J_w} + 1} · Φ` at every time of the window. -/
def WeakPassageComparisonHighStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A},
    A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1) →
    A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 < 2 * weakAStar B.α B.q * (A.Rw + 1) →
  ∀ (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → ∀ h : WeakComparisonInput r i,
    ∃ ehi : ∀ v : CompIn (c.stage i).comps, ℝ →
        TorusHk (weakComparisonReserve R v.1) (ScalarH v.1.root),
      (∀ v t, t ∈ Set.Icc (r.tq i) (r.a + A.T₀) →
        truncateTorusHk (Nat.zero_le _) (ehi v t) = h.e v t) ∧
      ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
        ∑ v, (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
            factorialNormSq (plan.radius R * c.D.eps i) (ehi v t).val ≤
          (plan.energyC R *
            (plan.forceC R * c.D.eps c.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) * h.Φ)) ^ 2

/-- A sum of extended reals whose square root is at most `ofReal X` has real value at most
`X²`, and every term is finite. -/
theorem sum_toReal_le_sq_of_sqrt_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {X : ℝ}
    (h : (∑ u ∈ s, f u) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal X) :
    (∀ u ∈ s, f u ≠ ⊤) ∧ ∑ u ∈ s, (f u).toReal ≤ X ^ 2 := by
  have h2 : ∑ u ∈ s, f u ≤ ENNReal.ofReal X ^ (2 : ℝ) := by
    have := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
    rwa [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at this
  have htop : ENNReal.ofReal X ^ (2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hfin : ∀ u ∈ s, f u ≠ ⊤ := fun u hu =>
    ne_top_of_le_ne_top htop ((Finset.single_le_sum (fun _ _ => zero_le) hu).trans h2)
  refine ⟨hfin, ?_⟩
  rw [← ENNReal.toReal_sum hfin]
  refine (ENNReal.toReal_mono htop h2).trans ?_
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal', Real.rpow_two]
  rcases le_total 0 X with hX | hX
  · rw [max_eq_left hX]
  · rw [max_eq_right hX, zero_pow two_ne_zero]
    exact sq_nonneg X

/-- **The weak passage comparison at the component reserves, from its residual**, for every
passage plan with the reserve, rows and energy plan conditions. -/
theorem weak_passage_comparison_high_of_residual (plan : WeakPassagePlan)
    (hplan : WeakComparisonReservePlanOK plan) (hrows : WeakComparisonRowsPlanOK plan)
    (hE : WeakComparisonEnergyPlanOK plan) (hres : WeakComparisonResidualStatement plan) :
    WeakPassageComparisonHighStatement plan := by
  intro B A R hN hR c r i hi hit h
  obtain ⟨F, g, Y, hFm, hgm, hsol, hcost⟩ := hres hN hR c r i hi hit h
  let hI : WeakComparisonEnergyInput r i := ⟨F, g, h.e, h.ew, Y, hFm, hgm, hsol⟩
  have hc : (∑ u, weakComparisonRowForcing hI u) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (plan.forceC R * c.D.eps c.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) * h.Φ) := hcost
  obtain ⟨hfin, hsum⟩ := sum_toReal_le_sq_of_sqrt_le Finset.univ _ hc
  obtain ⟨hd, hbound⟩ := weak_comparison_high_energy plan hplan hrows hE c r i hi hit hI
    (fun v => hfin v (Finset.mem_univ v))
  refine ⟨hd.e, hd.values, fun t ht => (hbound t ht).trans ?_⟩
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left hsum (sq_nonneg _)

/-- **The weak passage comparison at the component reserves, from its residual**, on the refined
passage plan `weakComparisonPassagePlan`. -/
theorem weak_passage_comparison_high_passage (plan : WeakPassagePlan)
    (hres : WeakComparisonResidualStatement (weakComparisonPassagePlan plan)) :
    WeakPassageComparisonHighStatement (weakComparisonPassagePlan plan) := by
  obtain ⟨hplan, -, hrows, hE⟩ := weakComparisonPassagePlan_ok plan
  exact weak_passage_comparison_high_of_residual _ hplan hrows hE hres

end AVRegularity.Providers.WeakGen.Comparison
end
end
