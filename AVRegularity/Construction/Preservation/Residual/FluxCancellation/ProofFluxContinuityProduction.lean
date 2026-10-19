-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCascadeFluxOrderBound
import AVRegularity.CycleComparison.Reconstruction.PulseChart
import AVRegularity.Construction.Preservation.Assembly.FullLiftFromInputs
import AVRegularity.Construction.Preservation.Frontier.GradeRows.ExtendedCertificates
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup
import AVRegularity.EntryWeak.NormalizedPulseTransverse

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVenhance AVRegularity
namespace AVRegularity.Construction.Preservation.Residual.FluxCancellation

/-! The path-sum step at positive grades: the decomposition for `Dm < 2` (`HLLowOrderStatement`), and
the piece.

For `Dm < 2` there is no source edge at all (`Finset.Icc 2 Dm` is empty), so:

* `hl_liftCellSource_eq_zero`: the cell source of a positive grade of arrays vanishing at the
  positive grades vanishes;
* `hl_lift_pos_grade_zero`: the positive grades of a lift sequence vanish on the window (its
  grade-zero part, extended by zero, is a lift sequence; uniqueness);
* `hl_lift_grade_zero_diag`: the grade zero of a lift sequence is the diagonal array of a scalar
  lift with no edge (`hlDiag_isLiftSequence`; uniqueness; any `Dm`);
* `hl_cand_zero`: the path-candidate array of grade zero is diagonal.

Hence the lift of the fibre and every path lift are the path-candidate arrays of the top entries:
at the grade zero both are the diagonal array of the lift of the empty path, at the positive grades
both vanish (`hl_lowOrder`). With `hl_zeroLift` this closes the assembly:
`hilbertLiftPathSum : HilbertLiftPathSumStatement`. -/

open CovarianceTransport CovFluxReg
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.HLZero
open AVRegularity.Providers.PathDecomp
open AVRegularity.CycleComparison.Reconstruction

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {hs : ι → Type}
  [∀ i, NormedAddCommGroup (hs i)] [∀ i, NormedSpace ℝ (hs i)] {Dm : ℕ}

omit [Fintype ι] [DecidableEq ι] in
/-- For `Dm < 2` there is no edge. -/
theorem hl_edge_nil (hDm : Dm < 2) (Q : LiftOperatorData ι hs Dm) (v u : ι)
    (d : Finset.Icc 2 Dm) : Q.edge v u d = [] :=
  absurd (Finset.mem_Icc.mp d.2) (by omega)

omit [DecidableEq ι] in
/-- With no edge, the cell source of a positive grade of arrays vanishing at the positive grades
vanishes. -/
theorem hl_liftCellSource_eq_zero (hDm : Dm < 2) (Q : LiftOperatorData ι hs Dm)
    {Cc : ℕ → ℕ → LiftCoeff ι hs} (hz : ∀ hh', hh' ≠ 0 → ∀ n, Cc hh' n = 0)
    (a : ℝ → Vec 2 → ∀ i, hs i) {hh : ℕ} (hh0 : hh ≠ 0) (n : ℕ) (t : ℝ) (X z : Vec 2) :
    liftCellSource Q Cc a hh n t X z = 0 := by
  have hA : ∀ hh', hh' ≠ 0 → ∀ n' X' z', liftA Q Cc a hh' n' t X' z' = 0 := by
    intro hh' h0 n' X' z'
    funext v
    refine liftA_apply_eq_zero (fun X'' z'' => ?_) (fun X'' z'' => ?_)
      (fun _ j u => Or.inl fun d => hl_edge_nil hDm Q v u d) X' z'
    · exact liftApply_apply_eq_zero fun m α u => Or.inl (by rw [hz hh' h0]; rfl)
    · exact liftApply_apply_eq_zero fun m α u => Or.inl (by rw [hz hh' h0]; rfl)
  have hM : ∀ hh', hh' ≠ 0 → ∀ n', liftMean Q Cc a hh' n' t = fun _ => 0 := by
    intro hh' h0 n'
    funext X'
    unfold liftMean
    rw [show (fun z' => liftA Q Cc a hh' n' t X' z') = fun _ => 0 from funext (hA hh' h0 n' X')]
    exact fieldCellMean_zero
  unfold liftCellSource
  rw [hA hh hh0, hM hh hh0]
  simp only [sub_self, neg_zero, zero_add]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun p hp => ?_
  funext v
  by_cases hp1 : p.1 = 0
  · have hp2 : p.2 ≠ 0 := by
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      omega
    exact liftApply_apply_eq_zero fun m α u => Or.inr fun X' => by rw [hM p.2 hp2]; rfl
  · exact liftApply_apply_eq_zero fun m α u => Or.inl (by rw [hz p.1 hp1]; rfl)

/-- The zero field is the cell inverse of the zero source. -/
theorem hl_isCellFieldInverse_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) {sZ : ℕ}
    (hsZ : 1 ≤ sZ) (t₀ t₁ : ℝ) :
    IsCellFieldInverse G v sZ t₀ t₁ (fun _ => (0 : E)) (fun _ _ => 0) (fun _ _ => 0) := by
  have h := isCellFieldInverse_sum_smul (E := E) (G := G) (v := v) hsZ (t₀ := t₀) (t₁ := t₁)
    (∅ : Finset Unit) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ => 0) (by simp)
  simpa using h

/-- The grade-zero part of coefficient arrays, extended by zero to the positive grades. -/
def hlGradeZeroPart (Cc : ℕ → ℕ → LiftCoeff ι hs) : ℕ → ℕ → LiftCoeff ι hs :=
  fun hh n => if hh = 0 then Cc 0 n else 0

omit [Fintype ι] [DecidableEq ι] in
theorem hlGradeZeroPart_zero (Cc : ℕ → ℕ → LiftCoeff ι hs) (n : ℕ) :
    hlGradeZeroPart Cc 0 n = Cc 0 n := by
  simp [hlGradeZeroPart]

omit [Fintype ι] [DecidableEq ι] in
theorem hlGradeZeroPart_pos (Cc : ℕ → ℕ → LiftCoeff ι hs) {hh : ℕ} (h : hh ≠ 0) (n : ℕ) :
    hlGradeZeroPart Cc hh n = 0 := by
  simp [hlGradeZeroPart, h]

omit [DecidableEq ι] in
/-- With no edge, the grade-zero part of a lift sequence is a lift sequence. -/
theorem hl_isLiftSequence_gradeZeroPart [∀ i, FiniteDimensional ℝ (hs i)] (hDm : Dm < 2)
    {Q : LiftOperatorData ι hs Dm} {sX sZ N H : ℕ} {t₀ t₁ : ℝ} {Cc : ℕ → ℕ → LiftCoeff ι hs}
    (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (hsZ : 1 ≤ sZ) :
    IsLiftSequence Q sX sZ t₀ t₁ N H (hlGradeZeroPart Cc) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a₀ ha₀ t ht X z
    rw [hlGradeZeroPart_zero]
    exact h0 a₀ ha₀ t ht X z
  · intro hh hh1 _ m α t X z v u
    rw [hlGradeZeroPart_pos Cc (by omega)]
    rfl
  · intro hh hhH n hn m α t X z v u
    by_cases hz : hh = 0
    · subst hz
      rw [hlGradeZeroPart_zero]
      exact h2 0 hhH n hn m α t X z v u
    · rw [hlGradeZeroPart_pos Cc hz]
      rfl
  · intro hh hhH n m hnm α t X z v u
    by_cases hz : hh = 0
    · subst hz
      rw [hlGradeZeroPart_zero]
      exact h3 0 hhH n m hnm α t X z v u
    · rw [hlGradeZeroPart_pos Cc hz]
      rfl
  · intro hh hhH n m α σ
    by_cases hz : hh = 0
    · subst hz
      rw [hlGradeZeroPart_zero]
      exact h4 0 hhH n m α σ
    · rw [hlGradeZeroPart_pos Cc hz]
      rfl
  · intro hh hhH n m α v u t ht
    by_cases hz : hh = 0
    · subst hz
      rw [hlGradeZeroPart_zero]
      exact h5 0 hhH n m α v u t ht
    · rw [hlGradeZeroPart_pos Cc hz]
      exact ⟨isBoxSmooth_zero sX sZ, fun X n' x => rfl⟩
  · intro hh hhH n hn1 hnN a₀ ha₀ X
    by_cases hz : hh = 0
    · subst hz
      have hc := h6 0 hhH n hn1 hnN a₀ ha₀ X
      rw [hlGradeZeroPart_zero]
      refine CycleComparison.Lift.cellFieldInverse_source_congr_on _ _ sZ t₀ t₁ _ _ _ _
        (fun t ht => ?_) hc
      funext z
      have IH : ∀ hh' n', (hh' < 0 ∨ (hh' = 0 ∧ n' < n)) →
          Uniqueness.CoeffEq Cc (hlGradeZeroPart Cc) t₀ t₁ hh' n' := by
        rintro hh' n' (h | ⟨rfl, h⟩)
        · omega
        · intro t _ m α
          rw [hlGradeZeroPart_zero]
      exact congrFun (congrFun
        (Uniqueness.liftCellSource_congr Q 0 n hn1 IH ht (fun _ => a₀)) X) z
    · have hs0 : (fun t z => liftCellSource Q (hlGradeZeroPart Cc) (fun _ => a₀) hh n t X z) =
          fun _ _ => 0 := funext fun t => funext fun z =>
        hl_liftCellSource_eq_zero hDm Q (fun hh' h' n' => hlGradeZeroPart_pos Cc h' n')
          (fun _ => a₀) hz n t X z
      have hf0 : (fun t z => liftApply n (hlGradeZeroPart Cc hh n) (fun _ => a₀) t X z) =
          fun _ _ => 0 := by
        funext t z v
        exact liftApply_apply_eq_zero fun m α u =>
          Or.inl (by rw [hlGradeZeroPart_pos Cc hz]; rfl)
      rw [hs0, hf0]
      exact hl_isCellFieldInverse_zero _ _ hsZ t₀ t₁

omit [DecidableEq ι] in
/-- **With no edge, the positive grades of a lift sequence vanish on the window.** -/
theorem hl_lift_pos_grade_zero [∀ i, FiniteDimensional ℝ (hs i)] (hDm : Dm < 2)
    (Q : LiftOperatorData ι hs Dm) {sX sZ N H : ℕ} {t₀ t₁ : ℝ} {Cc : ℕ → ℕ → LiftCoeff ι hs}
    (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (hab : t₀ ≤ t₁)
    (hW : ∀ X, ∃ lo A Mv : ℝ,
      Uniqueness.WindowData (fun t => Matrix.of (Q.G t X)) Q.v t₀ t₁ lo A Mv)
    (hsZ : 1 ≤ sZ) (hh : ℕ) (hz : hh ≠ 0) (hhH : hh ≤ H) (n m : ℕ) (α : DerivativeWord2 m)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) (X z : Vec 2) (v u : ι) :
    Cc hh n m α t X z v u = 0 := by
  have h := Uniqueness.lift_sequence_unique_window Q t₀ t₁ hab hW sX sZ N H Cc
    (hlGradeZeroPart Cc) hC (hl_isLiftSequence_gradeZeroPart hDm hC hsZ) hh hhH n m α t ht X z v u
  rw [h, hlGradeZeroPart_pos Cc hz]
  rfl

/-- **The grade zero of a lift sequence is the diagonal array of a scalar lift with no edge.** -/
theorem hl_lift_grade_zero_diag [∀ i, FiniteDimensional ℝ (hs i)] [∀ i, CompleteSpace (hs i)]
    (Q : LiftOperatorData ι hs Dm) (Q0 : LiftOperatorData (Fin 1) (fun _ : Fin 1 => ℝ) Dm)
    (hη : Q0.η = Q.η) (hG : Q0.G = Q.G) (hv : Q0.v = Q.v) {sX sZ N H : ℕ} {t₀ t₁ : ℝ}
    {Cc : ℕ → ℕ → LiftCoeff ι hs} (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    {C0 : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ : Fin 1 => ℝ)}
    (hC0 : IsLiftSequence Q0 sX sZ t₀ t₁ N 0 C0) (hab : t₀ ≤ t₁)
    (hW : ∀ X, ∃ lo A Mv : ℝ,
      Uniqueness.WindowData (fun t => Matrix.of (Q.G t X)) Q.v t₀ t₁ lo A Mv)
    (hsZ : 1 ≤ sZ) (hfX : N + 2 ≤ sX) (hfZ : N + 2 ≤ sZ)
    (hGs : ∀ t i j, ContDiff ℝ (⊤ : ℕ∞) (fun X => Q.G t X i j))
    (hvs : ∀ t k, ContDiff ℝ (⊤ : ℕ∞) (fun z => Q.v t z k))
    (n m : ℕ) (α : DerivativeWord2 m) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) (X z : Vec 2) (v u : ι) :
    Cc 0 n m α t X z v u = (C0 0 n m α t X z 0 0 1) • hlDiagMap hs v u := by
  have hD := hlDiag_isLiftSequence (hs := hs) C0 Q Q0 hη hG hv hC0 hab hsZ hfX hfZ hGs hvs
  have h := Uniqueness.lift_sequence_unique_window Q t₀ t₁ hab hW sX sZ N 0 Cc
    (hlDiagCoeff hs C0) (hC.restrict (Nat.zero_le H)) hD 0 le_rfl n m α t ht X z v u
  rw [h, hlDiagCoeff_apply_zero]

/-- The path-candidate array of grade zero is diagonal. -/
theorem hl_cand_zero (F : FamData ι hs) (T : (g : ℕ) → (Fin g → StepDat) → SArr) (n m : ℕ)
    (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2) (v u : ι) :
    cand F T 0 n m α t X z v u = T 0 Fin.elim0 n m α t X z • hlDiagMap hs v u := by
  classical
  unfold cand
  by_cases h : u = v
  · subst h
    have : Unique (F.Walk 0 u u) := ⟨⟨⟨rfl⟩⟩, fun q => by cases q; rfl⟩
    rw [Fintype.sum_unique, hlDiagMap_self]
    have hd : F.walkDat (default : F.Walk 0 u u) = Fin.elim0 := funext fun i => Fin.elim0 i
    rw [hd]
    rfl
  · have : IsEmpty (F.Walk 0 u v) := ⟨fun q => h q.down⟩
    rw [Fintype.sum_empty, hlDiagMap_ne (fun h' => h h'.symm), smul_zero]

end Generic

/-- **The decomposition for `Dm < 2`** (`HLLowOrderStatement`). -/
theorem hl_lowOrder : HLLowOrderStatement := by
  intro hr _ _ _ _ D Dm b j₀ P Mn G hin hE hsX hsZ ρ depth CcT k hk hadm hlift hne g hd Cπ hπ C0 hC0
    hDm
  classical
  have H := hl_setting hin hE hsX hsZ ρ hk hadm hne g Cπ hπ C0 hC0
  have hT := hl_hilbert_native hin ρ hk hadm hlift hd
  have hab := H.window
  have hsZ1 : 1 ≤ Mn.sZ := by omega
  -- the top arrays: the lift of the empty path at the grade zero, zero at the positive grades
  have hA0 : stArise G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) ⟨k, hk⟩
      ⟨nativeChain G.level k, hadm⟩ (g + 1) 0 Fin.elim0 :=
    ⟨Nat.zero_le _, ⟨⟨Fin.elim0, fun j hj => by omega⟩, funext fun i => i.elim0⟩⟩
  have hT0 : ∀ n m (α : DerivativeWord2 m) (t : ℝ) (X z : Vec 2),
      HLDecomp.hlTop G G.level ρ ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩ (g + 1) (hlLifts C0 Cπ) 0
        Fin.elim0 n m α t X z = C0 0 n m α t X z 0 0 1 := by
    intro n m α t X z
    show topOf _ _ 0 Fin.elim0 n m α t X z = _
    rw [StepHyp.topOf_of_arise hA0]
    simp only [topArr, stLift, dite_eq_left_of_eq_true (eq_true hA0)]
    rfl
  have hTpos : ∀ g', g' ≠ 0 → ∀ (cd : Fin g' → StepDat) n m (α : DerivativeWord2 m),
      ∀ t ∈ Set.Icc (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level),
      ∀ X z, HLDecomp.hlTop G G.level ρ ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩ (g + 1)
        (hlLifts C0 Cπ) g' cd n m α t X z = 0 := by
    intro g' h0 cd n m α t ht X z
    by_cases hA : stArise G (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) ⟨k, hk⟩
        ⟨nativeChain G.level k, hadm⟩ (g + 1) g' cd
    · show topOf _ _ g' cd n m α t X z = 0
      rw [StepHyp.topOf_of_arise hA]
      simp only [topArr]
      rw [hl_lift_pos_grade_zero hDm _ (H.lift_seq hA) hab H.windowData hsZ1 g' h0 le_rfl n m α ht
        X z (Fin.last g') 0]
      rfl
    · show topOf _ _ g' cd n m α t X z = 0
      simp [topOf, hA]
  refine ⟨fun g' hg' n t ht m α => ?_, fun L hL σ g' hg' n t ht m α => ?_⟩
  · funext X z v u
    by_cases h0 : g' = 0
    · subst h0
      rw [hl_cand_zero, hT0, hl_lift_grade_zero_diag
        (familyLiftData D G.level k (nativeChain G.level k) ρ
          (G.fam.fiber ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩))
        (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k (nativeChain G.level k)
          ρ (fun _ _ _ => [])) rfl rfl rfl hT hC0 hab H.windowData hsZ1 (by omega) (by omega)
        (fun t i j => EntryWeakProofs.familyLiftData_metric_entry_smooth D G.level k
          (nativeChain G.level k) rfl ρ _ t i j)
        (fun t c => hl_familyLiftData_drift_smooth D G.level k (nativeChain G.level k) ρ _ t c)
        n m α ht X z v u]
    · rw [hl_lift_pos_grade_zero hDm _ hT hab H.windowData hsZ1 g' h0 hg' n m α ht X z v u]
      symm
      unfold cand
      exact Finset.sum_eq_zero fun q _ => by rw [hTpos g' h0 _ n m α t ht X z, zero_smul]
  · funext X z v u
    by_cases h0 : g' = 0
    · subst h0
      rw [hl_cand_zero, hT0, hl_lift_grade_zero_diag
        (familyLiftData D G.level k (nativeChain G.level k) ρ
          (pathEdges G σ ⟨k, hk⟩ ⟨nativeChain G.level k, hadm⟩))
        (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k (nativeChain G.level k)
          ρ (fun _ _ _ => [])) rfl rfl rfl (H.hπ L hL σ) hC0 hab H.windowData hsZ1 (by omega)
        (by omega)
        (fun t i j => EntryWeakProofs.familyLiftData_metric_entry_smooth D G.level k
          (nativeChain G.level k) rfl ρ _ t i j)
        (fun t c => hl_familyLiftData_drift_smooth D G.level k (nativeChain G.level k) ρ _ t c)
        n m α ht X z v u]
    · rw [hl_lift_pos_grade_zero hDm _ (H.hπ L hL σ) hab H.windowData hsZ1 g' h0 hg' n m α ht
        X z v u]
      symm
      unfold cand
      exact Finset.sum_eq_zero fun q _ => by rw [hTpos g' h0 _ n m α t ht X z, zero_smul]

/-- **The path-sum step: the lift of the Hilbert fibre is the sum over the paths.** -/
theorem hilbertLiftPathSum : HilbertLiftPathSumStatement :=
  hilbertLiftPathSum_of_parts hilbertLiftGradeZero hl_zeroLift hl_lowOrder

end AVRegularity.Construction.Preservation.Residual.FluxCancellation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual

/-! The prefixed continuity statements of the readout fluxes: `R` from the retained stage
certificates, and `RO`, `RD`, `Pl` from `extended_successor_context_certified` (with the
reserves re-derived).
The two prefixed statements are over the frame predicates `ContROn` and `ContEOn`; the third part
(`N`) is the regularity piece. -/

open AVRegularity.Construction.Preservation.Assembly FullLift FluxCancellation CovarianceTransport

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Continuity of `R` on the window. -/
def ContROn (F : Frame D hr Dm b j₀) : Prop :=
  ∀ v : CompIn F.G.comps, ∀ t ∈ Set.Icc F.tp F.tf, Continuous (fluxR F v t)

/-- Continuity of `RO`, `RD`, `Pl` on the window. -/
def ContEOn (F : Frame D hr Dm b j₀) : Prop :=
  ∀ v : CompIn F.G.comps, ∀ t ∈ Set.Icc F.tp F.tf,
    Continuous (fluxRO F v t) ∧ Continuous (fluxRD F v t) ∧ Continuous (fluxPl F v t)

/-- A frame statement implied pointwise by another one is produced under the same prefix. -/
theorem FluxCancellation.frame_production_map {Q₁ Q₂ : FramePredicate} {α s q : ℝ}
    {ζ : ℝ → ℝ} (h : CovarianceTransportProductionStatement α s q ζ Q₁)
    (f : ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
      (F : Frame D hr Dm bw j₀), Q₁ F → Q₂ F) :
    CovarianceTransportProductionStatement α s q ζ Q₂ := by
  obtain ⟨Λ₀, hΛ₀, h⟩ := h
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ => ?_⟩
  obtain ⟨c, hc, h⟩ := h Λ hΛ
  refine ⟨c, hc, ?_⟩
  intro φ₀ hφ₀ h1 h2 h3 h4 bw hbw hbw' Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe a1 a2 a3 a4 a5 a6
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hfX hfZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, h⟩ := h φ₀ hφ₀ h1 h2 h3 h4 bw hbw hbw' Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe a1 a2 a3 a4 a5 a6 H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀
    a σ hsched hNaux hNout halloc hfX hfZ
  refine ⟨thr, CH, Υ, hCH, hΥ, fun kI hkI => ?_⟩
  obtain ⟨CIt, Cwt, h⟩ := h kI hkI
  refine ⟨CIt, Cwt, fun CI Cw j₀ hl hs => ?_⟩
  intro CQ Cpr
  obtain ⟨mStar, h⟩ := h CI Cw j₀ hl hs CQ Cpr
  refine ⟨mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f' Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  exact f _ (h D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
      seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA s₀ htA hs₀ htf hT₀ G G'
      hcascade hlevel hG hactual tp Preg hprep f' Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û
      hlift aZ aY hZ hY)

/-- **`R` is continuous**, from the retained stage certificates. -/
theorem fluxContR_production {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    CovarianceTransportProductionStatement α s q ζ ContROn := by
  classical
  obtain ⟨Λ₀, hΛ₀, hc⟩ := retained_stage_certificates α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ => ?_⟩
  obtain ⟨cmax, hcmax, hc⟩ := hc Λ hΛ
  refine ⟨cmax, hcmax, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hc⟩ := hc kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  obtain ⟨mc, hc⟩ := hc CI Cw j₀ hledger hstart
  refine ⟨max mc (j₀ + 2), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow _hT G G' hcascade hlevel hG hactual
    tp Preg hprep _f _Ain _hf Y0 Y Yw Yk _htrace hsol _CcT _PZ _aRep _û _hlift aZ aY hZ hY
  let P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p
  let Mn := succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)
  let Gr := G'.retained m H J
  have hlev : Gr.level = m - 1 := by
    change G'.level = m - 1
    rw [hactual.2.1, hlevel]
  have hcGr : IsCascadeStage D P Mn seed Gr := by
    simpa only [P, Mn, Gr, hlevel, succMenu] using IsCascadeStage.step hcascade hactual
  obtain ⟨hnat, _hshift, hslot, hctx, _hmarked, _hker⟩ := hc D hDα hDq hDΛ hDζ hseq M hband
    hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM
    tA htA G G' hcascade hlevel hG hactual
  obtain ⟨_hc0I, _hcrI, hprod⟩ := Buffer.invariantAdmissible_molecular_parameters hkI
  have hmGr v : 0 ≤ compReserve kI (v : CompIn Gr.comps).1 :=
    (Buffer.cascade_component_reserve_pos hseed.2.1 hcGr kI hprod v).le
  have hm2Gr v : compReserve kI (v : CompIn Gr.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hi : 1 ≤ Gr.level := by rw [hlev]; omega
  have hj : j₀ ≤ Gr.level := by rw [hlev]; omega
  have hε : 0 < D.eps (Gr.level - 1) :=
    Construction.Stream.ocEpsilon_pos (by rw [hDΛ]; omega)
  have haux := hsched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hDm : succSchedD D₀ N p (H + 1) ≤ Naux := by omega
  have hcoeff : ∀ v u (γ : Gr.fam.Γ v u) d, ∀ t ∈ Set.Icc tp tf,
      Continuous (Gr.physCoeff v u γ d t) := by
    intro v u γ d t ht
    exact (native_physCoeff_all_order_smooth hctx hslot hnat hi hj hbw hε tp tf
      v u γ (hmGr v) (hm2Gr v) 0 d t ht).continuous
  have hcs : HasCompactSupport φ₀ := Providers.hasCompactSupport_of_unitBall hφsupport
  intro v t ht
  exact fluxCont_R _ hφ₀ hφsmooth hcs hDm hcoeff v t ht

/-- **`RO`, `RD`, `Pl` are continuous**, from the context certificate of the extended successor. -/
theorem fluxContE_production {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    CovarianceTransportProductionStatement α s q ζ ContEOn := by
  classical
  obtain ⟨Λ₀, hΛ₀, hc⟩ := Frontier.extended_successor_context_certified α s hα₀ hα₁ hs₀ hs₁ q hq
    ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ => ?_⟩
  obtain ⟨cmax, hcmax, hc⟩ := hc Λ hΛ
  refine ⟨cmax, hcmax, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hc⟩ := hc kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  obtain ⟨mc, hc⟩ := hc CI Cw j₀ hledger hstart
  refine ⟨max mc (j₀ + 2), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow _hT G G' hcascade hlevel hG hactual
    tp Preg hprep _f _Ain _hf Y0 Y Yw Yk _htrace hsol _CcT _PZ _aRep _û _hlift aZ aY hZ hY
  obtain ⟨hslot, hctx⟩ := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw seedK
    freshK hfresh seed n tS tf hseed m (by omega) hn hnM G G' hcascade hlevel ⟨tA, htA, hG⟩ hactual
  obtain ⟨_hc0I, _hcrI, hprod⟩ := Buffer.invariantAdmissible_molecular_parameters hkI
  have hlev : G'.level = m - 1 := by rw [hactual.2.1, hlevel]
  have hnat : G'.IsNatural Mnat := hactual.2.2.2.1
  have hgr := Providers.CascadeInvariants.grade_le_of_succ
    (Providers.CascadeInvariants.grade_le_of_cascade hseed.2.1 hcascade) hactual
  have hmG v : 0 ≤ compReserve kI (v : CompIn G'.comps).1 :=
    Providers.CascadeInvariants.compReserve_nonneg_of_succ kI (H := H) hprod (hgr v)
  have hm2G v : compReserve kI (v : CompIn G'.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hi : 1 ≤ G'.level := by rw [hlev]; omega
  have hj : j₀ ≤ G'.level := by rw [hlev]; omega
  have hε : 0 < D.eps (G'.level - 1) :=
    Construction.Stream.ocEpsilon_pos (by rw [hDΛ]; omega)
  have haux := hsched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hDm : succSchedD D₀ N p (H + 1) ≤ Naux := by omega
  have hcoeff : ∀ v u (γ : G'.fam.Γ v u) d, ∀ t ∈ Set.Icc tp tf,
      Continuous (G'.physCoeff v u γ d t) := by
    intro v u γ d t ht
    exact (native_physCoeff_all_order_smooth hctx hslot hnat hi hj hbw hε tp tf
      v u γ (hmG v) (hm2G v) 0 d t ht).continuous
  have hcs : HasCompactSupport φ₀ := Providers.hasCompactSupport_of_unitBall hφsupport
  intro v t ht
  refine ⟨?_, ?_, ?_⟩
  · refine fluxCont_RO _ ?_ ?_ ?_ ?_ ?_ v t ht
    · exact hφ₀
    · exact hφsmooth
    · exact hcs
    · exact hDm
    · exact hcoeff
  · refine fluxCont_RD _ ?_ ?_ ?_ ?_ ?_ v t ht
    · exact hφ₀
    · exact hφsmooth
    · exact hcs
    · exact hDm
    · exact hcoeff
  · refine fluxCont_Pl _ ?_ ?_ ?_ ?_ ?_ v t ht
    · exact hφ₀
    · exact hφsmooth
    · exact hcs
    · exact hDm
    · exact hcoeff

end AVRegularity.Construction.Preservation.Residual
end
