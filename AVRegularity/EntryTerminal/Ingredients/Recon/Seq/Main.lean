-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeakAssembly.FiniteStagePaths
import AVRegularity.CycleReference.ChartTestTransport
import AVRegularity.EntryTerminal.Ingredients.Recon.R2Core.Quiet
import AVRegularity.Construction.ChildInert.Center
import AVRegularity.CycleComparison.Assembly.OcDiagonal
import AVRegularity.CycleComparison.LiftSetting.Main
public import AVRegularity.EntryTerminal.Ingredients.Recon.Coarse
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget

section
section
/-! # Lift sequences: the fibre of the actual family and the fibre of the stage agree on the output window

The fibre of `G.actualFamily` at a piece differs from the fibre of `G.fam` at the actual context only
by the coefficients, which are pinned to zero off the output window of the piece. So the source flux
of their lifted edges agree at every time whose physical time is in the output window. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Seq

theorem seq_listSum_filterMap_congr {a b M : Type*} [AddCommMonoid M] (l : List a)
    (f1 f2 : a → Option b) (ψ1 ψ2 : b → M)
    (h : ∀ x ∈ l, ((f1 x).map ψ1).getD 0 = ((f2 x).map ψ2).getD 0) :
    ((l.filterMap f1).map ψ1).sum = ((l.filterMap f2).map ψ2).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self)
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases e1 : f1 x with _ | y1 <;> rcases e2 : f2 x with _ | y2
    · simp only [List.filterMap_cons, e1, e2, hxs]
    · simp only [e1, e2, Option.map_none, Option.map_some, Option.getD_none,
        Option.getD_some] at hx
      simp only [List.filterMap_cons, e1, e2, List.map_cons, List.sum_cons, hxs, ← hx, zero_add]
    · simp only [e1, e2, Option.map_none, Option.map_some, Option.getD_none,
        Option.getD_some] at hx
      simp only [List.filterMap_cons, e1, e2, List.map_cons, List.sum_cons, hxs, hx, zero_add]
    · simp only [e1, e2, Option.map_some, Option.getD_some] at hx
      simp only [List.filterMap_cons, e1, e2, List.map_cons, List.sum_cons, hxs, hx]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The source flux of the lifted fibres agrees on the output window.** -/
theorem seq_sourceFlux_actual_eq (G : GenStage D hr Dm b j₀) (p : OddSlot) (c0 lam η ε t : ℝ)
    (ht : c0 * t ∈ (G.fam.piece p).output)
    (Φ : Vec 2 → Vec 2 → ∀ i : CompIn G.comps, hr i.1.root) (k : Fin 2) :
    sourceFlux (liftEdges c0 lam (G.fam.fiber p (G.actual p))) η ε t Φ k =
      sourceFlux (liftEdges c0 lam (G.actualFamily.fiber p ())) η ε t Φ k := by
  funext X z v
  unfold sourceFlux
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [liftEdges, ChartedFamily.fiber, List.map_map]
  refine seq_listSum_filterMap_congr _ _ _ _ _ fun γ _ => ?_
  by_cases hd : d.1 ≤ (G.fam.identity v u γ).maxOrder
  · simp [GenStage.actualFamily, hd, ht]
  · simp [GenStage.actualFamily, hd]

end AVRegularity.EntryTerminal.Ingredients.Recon.Seq
end
end

section
/-! # Lift sequences: a lift sequence only sees its operator data on the window

If two operator data agree (cell contrast, metric, drift, source flux) at the times of `[t₀, t₁]`,
then `IsLiftSequence` on `[t₀, t₁]` transfers from one to the other. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Seq

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- Agreement of two operator data at the time `t`: metric, drift and source flux. -/
def SeqAgreeAt (Q Q' : LiftOperatorData ι h D) (t : ℝ) : Prop :=
  Q.G t = Q'.G t ∧ Q.v t = Q'.v t ∧
    ∀ ε Φ k, sourceFlux Q.edge Q.η ε t Φ k = sourceFlux Q'.edge Q.η ε t Φ k

theorem seq_liftA_congr (Q Q' : LiftOperatorData ι h D) (hη : Q.η = Q'.η)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) {t : ℝ}
    (hag : SeqAgreeAt Q Q' t) : liftA Q Cc a hh n t = liftA Q' Cc a hh n t := by
  obtain ⟨η, G, v, e⟩ := Q
  obtain ⟨η', G', v', e'⟩ := Q'
  simp only at hη
  subst hη
  obtain ⟨hG, hv, he⟩ := hag
  dsimp only at hG hv he
  unfold liftA cellB1 cellB2 sourceCoeff sourceOp
  dsimp only
  simp only [hG, hv, he]

theorem seq_liftCellSource_congr (Q Q' : LiftOperatorData ι h D) (hη : Q.η = Q'.η)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) {t : ℝ}
    (hag : SeqAgreeAt Q Q' t) : liftCellSource Q Cc a hh n t = liftCellSource Q' Cc a hh n t := by
  have hA := seq_liftA_congr Q Q' hη Cc a
  have hM : ∀ hh n, liftMean Q Cc a hh n t = liftMean Q' Cc a hh n t := by
    intro hh n
    funext X
    simp only [liftMean, hA hh n hag]
  have hApp : ∀ (j : ℕ) (C : LiftCoeff ι h) (f g : ℝ → Vec 2 → ∀ i, h i), f t = g t →
      liftApply j C f t = liftApply j C g t := by
    intro j C f g hfg
    funext X z v
    simp only [liftApply, hfg]
  funext X z
  unfold liftCellSource
  rw [hA hh n hag]
  simp only [hM]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => ?_)
  rw [hApp j (Cc p.1 j) (liftMean Q Cc a p.2 (n - j)) (liftMean Q' Cc a p.2 (n - j))
    (hM p.2 (n - j))]

/-- A cell field inverse only sees the metric, the drift and the source on the window. -/
theorem seq_cellFieldInverse_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {G G' : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v v' : ℝ → Vec 2 → Vec 2}
    {sZ : ℕ} {t₀ t₁ : ℝ} {c₀ : Vec 2 → E} {g g' c : ℝ → Vec 2 → E}
    (hG : ∀ t ∈ Set.Icc t₀ t₁, G t = G' t) (hv : ∀ t ∈ Set.Icc t₀ t₁, v t = v' t)
    (hg : ∀ t ∈ Set.Icc t₀ t₁, g t = g' t) (h : IsCellFieldInverse G v sZ t₀ t₁ c₀ g c) :
    IsCellFieldInverse G' v' sZ t₀ t₁ c₀ g' c := by
  refine ⟨h.1, fun ℓ => ?_⟩
  obtain ⟨s1, s2, s3, s4⟩ := h.2 ℓ
  refine ⟨?_, s2, s3, s4⟩
  have s1' := AVRegularity.WeakEntryProofs.cellSolution_coefficients_congr_on (Set.Icc t₀ t₁)
    ⟨fun t _ => G t, v, 0, 0⟩ ⟨fun t _ => G' t, v', 0, 0⟩ _ _ _ rfl
    (fun r hr => ⟨fun _ => hG r hr, fun x => congrFun (hv r hr) x, rfl⟩) s1
  refine cellSolution_source_congr_sections (Set.Icc t₀ t₁) _ _ _ _ _ _ ?_ ?_ s1'
  · refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun r hr => ?_)
    exact Filter.EventuallyEq.of_eq (funext fun x => by simp [hg r hr])
  · exact Filter.Eventually.of_forall fun r => Filter.EventuallyEq.rfl

variable [∀ i, FiniteDimensional ℝ (h i)]

/-- **A lift sequence only sees its operator data on the window.** -/
theorem seq_isLiftSequence_congr (Q Q' : LiftOperatorData ι h D) (hη : Q.η = Q'.η)
    {sX sZ N H : ℕ} {t₀ t₁ : ℝ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hag : ∀ t ∈ Set.Icc t₀ t₁, SeqAgreeAt Q Q' t)
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) : IsLiftSequence Q' sX sZ t₀ t₁ N H Cc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hseq
  refine ⟨h1, h2, h3, h4, h5, h6, fun hh hhH n hn1 hnN a₀ ha₀ X => ?_⟩
  refine seq_cellFieldInverse_congr (fun t ht => ?_) (fun t ht => (hag t ht).2.1)
    (fun t ht => ?_) (h7 hh hhH n hn1 hnN a₀ ha₀ X)
  · funext i j
    simp [(hag t ht).1]
  · funext z
    rw [seq_liftCellSource_congr Q Q' hη Cc _ hh n (hag t ht)]

end AVRegularity.EntryTerminal.Ingredients.Recon.Seq
end
end
end

section
section
/-! # Lift sequences, step 1: the stage's lift data of the slot `k` and the lift data of the window

At a context, `c_r = 1`: the lift data `familyLiftData` of the slot `k` of the weak stage (the data
of `c.lift.1 k`) and `rLiftData c k` have the same cell contrast, metric and drift at every time,
and the same source flux at the times of the pulse window `= (piece k).output`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Seq

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
    Ce cker j₀ M)

/-- The stage's lift data of the odd slot `k` (the data of `c.lift.1 k`). -/
abbrev seqQ (k : ℤ) (hk : Odd k) :
    LiftOperatorData (CompIn c.Gw.comps) (fun v => ScalarH v.1.root) A.Dt :=
  familyLiftData c.D M k (nativeChain M k) (cr * liftLength c.D M)
    (c.Gw.fam.fiber ⟨k, hk⟩ (c.Gw.actual ⟨k, hk⟩))

/-- The output window of a piece of the weak stage is the pulse window. -/
theorem seq_output_eq (p : OddSlot) :
    (c.Gw.fam.piece p).output = ocPulseWindow c.D.α c.D.q c.D.Λ M p.1 := by
  have hlev : c.Gw.level = M := c.weak.2.2.1
  have := (c.weak.2.2.2.2.2.2.2.2.2.1.1 p).2.1
  simp only [hlev] at this
  exact this

/-- **Step 1: the stage's data and the window's data agree.** -/
theorem seq_agree (hone : cr = 1) (hΛ : 1 ≤ A.Λ) (hM : 1 ≤ M) {k : ℤ} (hk : Odd k) :
    (seqQ c k hk).η = (rLiftData c k).η ∧
      ∀ t, c.D.cellScaleSq M * t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ M k →
        SeqAgreeAt (seqQ c k hk) (rLiftData c k) t := by
  obtain ⟨hα, hq, hΛD, hζ, -, hchain, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ hΛ
  have hch : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ M c.D.κ := by
    rw [hα, hq, hΛD, hζ]; exact hchain
  have hκM : 0 < c.D.κ M := CycleReference.bandChain_pos hΛ1 (hζ ▸ X.hζ) hch le_rfl
  have hκM1 : 0 < c.D.κ (M - 1) := CycleReference.bandChain_pos hΛ1 (hζ ▸ X.hζ) hch (Nat.sub_le M 1)
  have hτ'' : 0 < ocTauPP c.D.α c.D.q c.D.Λ M := Construction.Stream.ocTauPP_pos hΛ1
  have hkap : c.D.kap M = c.D.κ M := by unfold OCData.kap; rw [hterm, min_self]
  have hkap1 : c.D.kap (M - 1) = c.D.κ (M - 1) := by
    unfold OCData.kap; rw [hterm, min_eq_left (Nat.sub_le M 1)]
  have hρ : cr * liftLength c.D M = rRho c :=
    (congrArg (· * liftLength c.D M) hone).trans (one_mul _)
  have hc : ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2 = c.D.cellScaleSq M := by
    rw [CycleReference.ocEll_sq_eq hκM]; unfold OCData.cellScaleSq OCData.eps; rw [hkap]
  have hη : (seqQ c k hk).η = (rLiftData c k).η := by
    show c.D.kap M / c.D.kap (M - 1) = c.D.κ M / c.D.κ (M - 1)
    rw [hkap, hkap1]
  refine ⟨hη, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · funext X' i j
    show (familyLiftData c.D M k (nativeChain M k) (cr * liftLength c.D M) _).G t X' i j = _
    rw [EntryWeakProofs.native_familyLiftData_metric c.D M hM k _ _ t X', hρ]
    show _ = ocMaterialMetric c.D.α c.D.q c.D.Λ M (c.D.Φ (M - 1)) (c.D.hΦ (M - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ M k) (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2 * t)
      (rRho c • X') i j
    unfold ocMaterialMetric ocChart OCData.flowOf OCData.slotAnchor
    rw [hc, ocLabel_eq_ocPulseChartIndex c.D.α c.D.q c.D.Λ M k hτ'']
  · funext z
    show ocPulseCellDrift c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.kap M) k t z = _
    rw [hkap]
    rfl
  · intro ε Φ i
    have hout : c.D.cellScaleSq M * t ∈ (c.Gw.fam.piece ⟨k, hk⟩).output := by
      rw [seq_output_eq c]; exact ht
    have key := seq_sourceFlux_actual_eq c.Gw ⟨k, hk⟩ (c.D.cellScaleSq M)
      (cr * liftLength c.D M / c.D.eps (M - 1)) (seqQ c k hk).η ε t hout Φ i
    have e2 : (rLiftData c k).edge = liftEdges (c.D.cellScaleSq M)
        (cr * liftLength c.D M / c.D.eps (M - 1)) (c.Gw.actualFamily.fiber ⟨k, hk⟩ ()) := by
      show liftEdges (ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2) (rRho c / ocEpsilon c.D.q c.D.Λ (M - 1))
        (c.Gw.actualFamily.fiber (oddSlotOf k) ()) = _
      rw [oddSlotOf_of_odd hk, hc, hρ]
      rfl
    rw [e2]
    exact key

end AVRegularity.EntryTerminal.Ingredients.Recon.Seq
end
end

section
/-! # Lift sequences, step 2: the positive lifts of the slot vanish at `t_p`

For a pulse `k` whose window contains `t_p` (`slotStart ≤ t_p ≤ (k + 61/48) τ`; the half-width
`61/48` is larger than the cutoff support `5/4`, and only `t_p ≤ (k + 61/48) τ` is used), the stretch
`[slotStart, t_p]` lies in the quiet margin (`τ' = L τ`, `L ≥ 5`, so `t_p - slotStart ≤ 61τ/24`)
and in `[a_M, a + T₀]` (the entrance). There the pulse drift vanishes and the edges are fast
independent (the stage invariant), so `r2c_quietZero_core` gives zero positive lifts at `t_p`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison

namespace AVRegularity.EntryTerminal.Ingredients.Recon.Seq

/-- The quiet margin geometry: between `t_p - 61τ/24` and `t_p` the `τ/24`-neighbourhood lies in the
quiet margin of half-width `Lτ`, and the time is at least `a_M`. -/
theorem seq_geometry {τ L tp kr aM : ℝ} (hτ : 0 < τ) (hL : 5 ≤ L)
    (hwin : tp ≤ (kr + 61 / 48) * τ) (haM : aM + L * τ ≤ tp) :
    ∀ u ∈ Set.Icc ((kr - 61 / 48) * τ) tp,
      Set.Icc (u - τ / 24) (u + τ / 24) ⊆ Set.Icc (tp - L * τ) (tp + L * τ) ∧ aM ≤ u := by
  have hLτ : 5 * τ ≤ L * τ := by nlinarith
  intro u hu
  refine ⟨fun y hy => ⟨by linarith [hu.1, hy.1], by linarith [hu.2, hy.2]⟩, by linarith [hu.1]⟩

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
    Ce cker j₀ M)

/-- **Step 2: the positive lifts of the slot `k` vanish at the cell time of `t_p`.** -/
theorem seq_zero_at_tp (x : TermResAux c) (hΛ : 1 ≤ A.Λ) {k : ℤ} (hk : Odd k)
    (hentry : c.aM + ocTauP c.D.α c.D.q c.D.Λ M ≤ c.tp) (htp : c.tp ≤ c.a + A.T₀)
    (hwin : c.tp ≤ ((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ M)
    (hstart : c.D.slotStart M k ≤ c.tp)
    (hell : ∀ t ∈ Set.Icc (c.D.slotStart M k / c.D.cellScaleSq M)
        ((((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ M) / c.D.cellScaleSq M),
      ∀ X' ξ : Vec 2,
        (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, (seqQ c k hk).G t X' i j * ξ i * ξ j ∧
        ∑ i, ∑ j, (seqQ c k hk).G t X' i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2)
    (hseq : IsLiftSequence (seqQ c k hk) sXT sZT (c.D.slotStart M k / c.D.cellScaleSq M)
      ((((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ M) / c.D.cellScaleSq M) A.NT A.dW
      (c.CcT k)) :
    ∀ hh ≤ A.dW, ∀ n, 1 ≤ n → ∀ m (α : DerivativeWord2 m) X' z v u,
      c.CcT k hh n m α (c.tp / c.D.cellScaleSq M) X' z v u = 0 := by
  classical
  obtain ⟨hα, hq, hΛD, hζ, -, hchain, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ hΛ
  have hlev : c.Gw.level = M := c.weak.2.2.1
  have hinv := c.weak.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfast, -⟩ := hinv
  have hfastM : c.Gw.fam.IsFastIndependentOn
      (ocTrimmedQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ M ∩ Set.Icc c.aM (c.a + A.T₀)) := by
    simpa only [hlev] using hfast
  have hch : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ M c.D.κ := by
    rw [hα, hq, hΛD, hζ]; exact hchain
  have hκM : 0 < c.D.κ M := CycleReference.bandChain_pos hΛ1 (hζ ▸ X.hζ) hch le_rfl
  have hkap : c.D.kap M = c.D.κ M := by unfold OCData.kap; rw [hterm, min_self]
  have hcs : 0 < c.D.cellScaleSq M := by
    unfold OCData.cellScaleSq OCData.eps
    rw [hkap]
    exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ1) 2) hκM
  have hsq : ocEll c.D.q c.D.Λ M (c.D.kap M) ^ 2 = c.D.cellScaleSq M := by
    rw [CycleReference.ocEll_sq_eq (hkap ▸ hκM)]; rfl
  have hτ : 0 < ocTau c.D.α c.D.q c.D.Λ M := Construction.Stream.ocTau_pos hΛ1
  have hLge := ChildInert.ocL_ge_five c.D.α c.D.q hΛ1 M
  have hTP : ocTauP c.D.α c.D.q c.D.Λ M = (ocL c.D.α c.D.q c.D.Λ M : ℝ) * ocTau c.D.α c.D.q c.D.Λ M := by
    have h5 : (0 : ℝ) < ocL c.D.α c.D.q c.D.Λ M := by linarith
    unfold ocTauP ocTau
    field_simp
  have hentry' : c.aM + (ocL c.D.α c.D.q c.D.Λ M : ℝ) * ocTau c.D.α c.D.q c.D.Λ M ≤ c.tp := by
    rw [← hTP]; exact hentry
  have hcol : Set.Icc (c.tp - (ocL c.D.α c.D.q c.D.Λ M : ℝ) * ocTau c.D.α c.D.q c.D.Λ M)
      (c.tp + (ocL c.D.α c.D.q c.D.Λ M : ℝ) * ocTau c.D.α c.D.q c.D.Λ M) ⊆
      ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ M := by rw [← hTP]; exact x.quietMargin
  have hss : c.D.slotStart M k = ((k : ℝ) - 61 / 48) * ocTau c.D.α c.D.q c.D.Λ M := rfl
  have hgeo := seq_geometry hτ hLge hwin hentry'
  -- the points of the stretch
  have hpt : ∀ t ∈ Set.Icc (c.D.slotStart M k / c.D.cellScaleSq M) (c.tp / c.D.cellScaleSq M),
      c.D.cellScaleSq M * t ∈ ocTrimmedQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ M ∩
        Set.Icc c.aM (c.a + A.T₀) ∧ c.D.cellScaleSq M * t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ M k ∧
        c.D.slotStart M k ≤ c.D.cellScaleSq M * t ∧ c.D.cellScaleSq M * t ≤ c.tp := by
    intro t ht
    have h1 : c.D.slotStart M k ≤ c.D.cellScaleSq M * t := by
      have := (div_le_iff₀ hcs).1 ht.1
      linarith
    have h2 : c.D.cellScaleSq M * t ≤ c.tp := by
      have := (le_div_iff₀ hcs).1 ht.2
      linarith
    obtain ⟨hg1, hg2⟩ := hgeo _ ⟨by rw [← hss]; exact h1, h2⟩
    refine ⟨⟨fun y hy => hcol (hg1 hy), hg2, h2.trans htp⟩, ⟨?_, h2.trans hwin⟩, h1, h2⟩
    · rw [hss] at h1; exact h1
  have hsC : c.D.slotStart M k / c.D.cellScaleSq M ≤ c.tp / c.D.cellScaleSq M :=
    div_le_div_of_nonneg_right hstart hcs.le
  have hend : c.tp / c.D.cellScaleSq M ≤
      (((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ M) / c.D.cellScaleSq M :=
    div_le_div_of_nonneg_right hwin hcs.le
  intro hh hhH n hn m α X' z v u
  refine r2c_quietZero_core (seqQ c k hk) sXT sZT A.NT A.dW _ _ _ (c.CcT k) hseq hsC hend
    (fun t X'' i j => EntryWeakProofs.familyLiftData_metric_symmetric c.D M k _ _ _ t X'' i j)
    ⟨3 / 4, 5 / 4, by norm_num, fun t ht X'' ξ => hell t ⟨ht.1, ht.2.trans hend⟩ X'' ξ⟩
    (fun t ht z => ?_) (fun t ht v' u' d γ hγ w X'' z z' => ?_) hh hhH n hn m α _ ⟨hsC, le_rfl⟩
    X' z v u
  · -- the drift vanishes
    have h0 : ocPulse c.D.α c.D.q c.D.Λ c.D.ζ M k (c.D.cellScaleSq M * t) = 0 :=
      Assembly.ocPulse_eq_zero_of_quiet hΛ1 (hζ ▸ X.hζ) hk
        (ocTrimmedQuietTimes_subset_quiet hΛ1 c.D.ζ M (hpt t ht).1.1)
    show ocPulseCellDrift c.D.α c.D.q c.D.Λ c.D.ζ M (c.D.kap M) k t z = 0
    unfold ocPulseCellDrift
    rw [hsq, h0]
    simp only [zero_smul, smul_zero]
  · -- the edges are fast independent
    have hγ' : γ ∈ liftEdges (c.D.cellScaleSq M)
        (cr * liftLength c.D M / c.D.eps (M - 1))
        (c.Gw.fam.fiber ⟨k, hk⟩ (c.Gw.actual ⟨k, hk⟩)) v' u' d := hγ
    obtain ⟨γ₀, -, -, hc⟩ := LiftSetting.mem_liftEdges_fiber hγ'
    have hmem := hpt t ht
    have hout : c.D.cellScaleSq M * t ∈ (c.Gw.fam.piece ⟨k, hk⟩).output := by
      rw [seq_output_eq c]; exact hmem.2.1
    rw [hc]
    exact hfastM ⟨k, hk⟩ (c.Gw.actual ⟨k, hk⟩) v' u' γ₀ d.1 w (c.D.cellScaleSq M * t)
      ⟨hmem.1, hout⟩ _ z z'

end AVRegularity.EntryTerminal.Ingredients.Recon.Seq
end
end

section
/-! # The lift sequences of the window, restarted at `t_p`

`reconSeqStep_of_ctx`: at a context with `c_r = 1`, `Λ ≥ 1`, `M ≥ 1` and the ellipticity of the
stage's lift metric on the slot windows, the sequence `c.lift.1 k` restricted (pulse window starting
after `t_p`) or restarted at `t_p` (pulse window containing `t_p`: zero positive lifts by the quiet
stretch, `Seq.Quiet`) is the lift sequence of `rLiftData c k` on the clipped window (`Seq.Data`,
`Seq.Congr`), at the lower orders (`isLiftSequence_mono`). `termReconSeq` through the prefix: the
ellipticity holds for `M ≥ M₁ + 1`, `M₁` from `uniform_native_lift_ellipticity_all_carriers`.

Special cases:
- no pulse window contains `t_p`: only the restriction.
- `t_p = slotStart`: both branches agree. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
open AVRegularity.CycleComparison.Reconstruction

namespace AVRegularity.EntryTerminal.Ingredients.Recon

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The ellipticity of the stage's lift metric on the slot windows (from the uniform native
ellipticity for large `M`). -/
def SeqEll (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
    Ce cker j₀ M) : Prop :=
  ∀ (k : ℤ) (hk : Odd k), ∀ t ∈ Set.Icc (c.D.slotStart M k / c.D.cellScaleSq M)
        ((((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ M) / c.D.cellScaleSq M),
      ∀ X' ξ : Vec 2,
        (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, (Seq.seqQ c k hk).G t X' i j * ξ i * ξ j ∧
        ∑ i, ∑ j, (Seq.seqQ c k hk).G t X' i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2

/-- **The lift sequences at a context.** -/
theorem reconSeqStep_of_ctx
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (ℓ : ℕ) (hΛ : 1 ≤ A.Λ) (hM : 1 ≤ M) (hell : SeqEll c) :
    ReconSeqStep c x ℓ := by
  classical
  intro hX hZ hentry k hkobs
  obtain ⟨hα, hq, hΛD, hζ, -, hchain, hterm⟩ := c.data
  have hΛ1 : 1 ≤ c.D.Λ := hΛD ▸ hΛ
  have hch : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ M c.D.κ := by
    rw [hα, hq, hΛD, hζ]; exact hchain
  have hκM : 0 < c.D.κ M := CycleReference.bandChain_pos hΛ1 (hζ ▸ X.hζ) hch le_rfl
  have hkap : c.D.kap M = c.D.κ M := by unfold OCData.kap; rw [hterm, min_self]
  have hcs : 0 < c.D.cellScaleSq M := by
    unfold OCData.cellScaleSq OCData.eps
    rw [hkap]
    exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ1) 2) hκM
  have hc : ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2 = c.D.cellScaleSq M := by
    rw [CycleReference.ocEll_sq_eq hκM]; unfold OCData.cellScaleSq OCData.eps; rw [hkap]
  have hτ : 0 < ocTau c.D.α c.D.q c.D.Λ M := Construction.Stream.ocTau_pos hΛ1
  obtain ⟨-, hk, y, ⟨hy1, hy2⟩, hy3, hy4⟩ := Finset.mem_filter.1 hkobs
  have hTobs : c.tp + rTobs c = c.a + A.T₀ := by unfold rTobs; ring
  -- the window
  set τ := ocTau c.D.α c.D.q c.D.Λ M with hτdef
  have hlo : rSeqStart c k = max (((k : ℝ) - 61 / 48) * τ) c.tp / c.D.cellScaleSq M := by
    unfold rSeqStart; rw [hc]
  have hhi : rSeqEnd c k = min (((k : ℝ) + 61 / 48) * τ) (c.tp + rTobs c) / c.D.cellScaleSq M := by
    unfold rSeqEnd; rw [hc]
  have hseq0 := c.lift.1 k hk
  have hAB : ((k : ℝ) - 61 / 48) * τ ≤ ((k : ℝ) + 61 / 48) * τ := by nlinarith
  have hmem : ∀ t ∈ Set.Icc (rSeqStart c k) (rSeqEnd c k),
      c.D.cellScaleSq M * t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ M k := by
    intro t ht
    rw [hlo] at ht; rw [hhi] at ht
    have h1 := (div_le_iff₀ hcs).1 ht.1
    have h2 := (le_div_iff₀ hcs).1 ht.2
    have e : t * c.D.cellScaleSq M = c.D.cellScaleSq M * t := mul_comm _ _
    exact ⟨(((le_max_left _ _).trans h1).trans_eq e), (e.symm.le.trans h2).trans (min_le_left _ _)⟩
  have hhi_le : rSeqEnd c k ≤
      (((k : ℝ) + 61 / 48) * τ) / c.D.cellScaleSq M := by
    rw [hhi]; exact div_le_div_of_nonneg_right (min_le_left _ _) hcs.le
  have hseq1 : IsLiftSequence (Seq.seqQ c k hk) sXT sZT (rSeqStart c k) (rSeqEnd c k) A.NT A.dW
      (c.CcT k) := by
    by_cases hcase : c.tp ≤ ((k : ℝ) - 61 / 48) * τ
    · have hl : rSeqStart c k = c.D.slotStart M k / c.D.cellScaleSq M := by
        rw [hlo, max_eq_left hcase]; rfl
      rw [hl]
      exact R2Core.r2c_liftSequence_restrict_right hseq0 hhi_le
    · have hcase' : c.D.slotStart M k ≤ c.tp := (not_le.1 hcase).le
      have hl : rSeqStart c k = c.tp / c.D.cellScaleSq M := by
        rw [hlo, max_eq_right (not_le.1 hcase).le]
      have hzero := Seq.seq_zero_at_tp c x hΛ hk hentry (by linarith) (by linarith) hcase'
        (hell k hk) hseq0
      rw [hl]
      exact R2Core.r2c_liftSequence_restart hseq0 (div_le_div_of_nonneg_right hcase' hcs.le)
        hhi_le hzero
  obtain ⟨hη, hag⟩ := Seq.seq_agree c x.one hΛ hM hk
  exact isLiftSequence_mono (Seq.seq_isLiftSequence_congr _ _ hη
    (fun t ht => hag t (hmem t ht)) hseq1) hX hZ

/-- The uniform native ellipticity gives `SeqEll` at a context for `M` above the threshold. -/
theorem seqEll_of_uniform
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) {M₁ : ℕ}
    (hell : ∀ (ι : Type) (h : ι → Type) [∀ i, NormedAddCommGroup (h i)]
      [∀ i, NormedSpace ℝ (h i)] (Dm : ℕ), ∀ D : OCData,
      D.α = X.α → D.q = X.q → D.Λ = A.Λ → D.ζ = X.ζ → IsOCStreamSeq X.α X.q A.Λ X.ζ D.Φ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ m, M₁ + 1 ≤ m → ∀ slot : ℤ, Odd slot →
      ∀ (ρ : ℝ) (edge : ConstituentEdges Dm h),
      ∀ t ∈ Set.Icc (D.slotStart m slot / D.cellScaleSq m)
        ((((slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m),
      ∀ X ξ : Vec 2,
        (3 / 4) * ∑ i, ξ i ^ 2 ≤
          ∑ i, ∑ j, (familyLiftData D m slot (nativeChain m slot) ρ edge).G t X i j * ξ i * ξ j ∧
        ∑ i, ∑ j, (familyLiftData D m slot (nativeChain m slot) ρ edge).G t X i j * ξ i * ξ j ≤
          (5 / 4) * ∑ i, ξ i ^ 2)
    (hM : M₁ + 1 ≤ M) : SeqEll c := by
  obtain ⟨hα, hq, hΛD, hζ, hseq, hchain, hterm⟩ := c.data
  intro k hk t ht X' ξ
  exact hell (CompIn c.Gw.comps) (fun v => ScalarH v.1.root) A.Dt c.D hα hq hΛD hζ
    hseq
    (by rw [hterm, hα, hq, hΛD, hζ]; exact hchain) M hM k hk _ _ t ht X' ξ

/-- **The lift sequences of the window with the prefix.** -/
theorem termReconSeq : TermReconSeqStatement := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ _ ℓ => ?_⟩
  obtain ⟨M₁, hM₁, hell⟩ := Construction.Preservation.FullLift.uniform_native_lift_ellipticity_all_carriers
    X.α X.s X.q X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq A.Λ (by omega) X.ζ X.hζ
  refine ⟨0, fun kc _ => ⟨rKlift A ℓ + A.Dt + 2, max (rLlift A ℓ + 1) (rLlift A ℓ + 2), 0,
    fun sXT sZT _ _ Kout _ => ⟨0, ?_⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker _
  exact ⟨(), 1, 1, le_rfl, one_pos, fun j₀ _ => ⟨M₁ + 1, fun M hM c x =>
    reconSeqStep_of_ctx c x ℓ (by omega) (by omega) (seqEll_of_uniform c hell hM)⟩⟩

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end
