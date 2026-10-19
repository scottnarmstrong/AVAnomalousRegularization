-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.IsLiftSequence
import AVRegularity.Construction.InitialLayer.Comparison
import AVRegularity.CycleComparison.Lift.DiagonalMeanLeftTermsActionOfCoefficients
import AVRegularity.CycleComparison.Residual.TailJets
import AVRegularity.Construction.Uniqueness.SuccessorFluxUnique

section
section
/-! # Lift-sequence core, fast independence of the lift operators

The operators of the lift recursion (`cellB1`, `cellB2`, `sourceCoeff`) map fields independent of the
fast variable to fields independent of the fast variable, when the drift vanishes and the edge
coefficients are fast independent. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Ingredients.Recon.R2Core

/-- `Φ(X,z)` does not depend on `z`. -/
def R2ZInd {E : Type*} (Φ : Vec 2 → Vec 2 → E) : Prop := ∀ X z z', Φ X z = Φ X z'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem r2c_slowPartial_zind {Φ : Vec 2 → Vec 2 → E} (hΦ : R2ZInd Φ) (i : Fin 2) :
    R2ZInd (slowPartial i Φ) := by
  intro X z z'
  have : (fun X' => Φ X' z) = fun X' => Φ X' z' := funext fun X' => hΦ X' z z'
  unfold slowPartial
  rw [this]

theorem r2c_fastPartial_zero {Φ : Vec 2 → Vec 2 → E} (hΦ : R2ZInd Φ) (i : Fin 2) (X z : Vec 2) :
    fastPartial i Φ X z = 0 := by
  have : (fun z' => Φ X z') = fun _ => Φ X 0 := funext fun z' => hΦ X z' 0
  unfold fastPartial
  rw [this]
  simp

theorem r2c_dEps_zind {Φ : Vec 2 → Vec 2 → E} (hΦ : R2ZInd Φ) (η ε : ℝ) (i : Fin 2) :
    R2ZInd (dEps η ε i Φ) := by
  intro X z z'
  simp only [dEps]
  rw [r2c_fastPartial_zero hΦ, r2c_fastPartial_zero hΦ, r2c_slowPartial_zind hΦ i X z z']

theorem r2c_foldl_dEps_zind (η ε : ℝ) :
    ∀ (l : List (Fin 2)) (Φ : Vec 2 → Vec 2 → E), R2ZInd Φ →
      R2ZInd (l.foldl (fun Ψ' i => dEps η ε i Ψ') Φ)
  | [], _, h => h
  | i :: l, _, h => r2c_foldl_dEps_zind η ε l _ (r2c_dEps_zind h η ε i)

theorem r2c_dEpsWord_zind {Φ : Vec 2 → Vec 2 → E} (hΦ : R2ZInd Φ) (η ε : ℝ) {m : ℕ}
    (α : DerivativeWord2 m) : R2ZInd (dEpsWord η ε α Φ) :=
  r2c_foldl_dEps_zind η ε _ _ hΦ

section Source

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}

theorem r2c_sourceFlux_zind (edge : ConstituentEdges Dm h) (η ε t : ℝ)
    (hedge : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : R2ZInd Φ) (k : Fin 2) :
    R2ZInd (sourceFlux edge η ε t Φ k) := by
  intro X z z'
  funext v
  unfold sourceFlux
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun d _ => ?_
  congr 1
  refine List.map_congr_left fun γ hγ => ?_
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hedge v u d γ hγ α X z z', r2c_dEpsWord_zind hΦ η ε α X z z']

theorem r2c_sourceOp_zind (edge : ConstituentEdges Dm h) (η ε t : ℝ)
    (hedge : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : R2ZInd Φ) :
    R2ZInd (sourceOp edge η ε t Φ) := by
  intro X z z'
  unfold sourceOp
  exact Finset.sum_congr rfl fun k _ =>
    r2c_dEps_zind (r2c_sourceFlux_zind edge η ε t hedge hΦ k) η ε k X z z'

theorem r2c_sourceCoeff_zind (edge : ConstituentEdges Dm h) (η t : ℝ) (j : ℕ)
    (hedge : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : R2ZInd Φ) :
    R2ZInd (sourceCoeff edge η j t Φ) := by
  intro X z z'
  unfold sourceCoeff
  have : (fun ε : ℝ => sourceOp edge η ε t Φ X z) = fun ε => sourceOp edge η ε t Φ X z' :=
    funext fun ε => r2c_sourceOp_zind edge η ε t hedge hΦ X z z'
  rw [this]

end Source

theorem r2c_cellB1_zind (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (t : ℝ) (hv : ∀ z, v t z = 0) {Φ : Vec 2 → Vec 2 → E} (hΦ : R2ZInd Φ) :
    R2ZInd (cellB1 η G v t Φ) := by
  intro X z z'
  have h1 : ∀ j, R2ZInd (slowPartial j Φ) := fun j => r2c_slowPartial_zind hΦ j
  have h2 : ∀ i j, R2ZInd (fun X' z' => G t X' i j • fastPartial j Φ X' z') := fun i j X' a b => by
    simp [r2c_fastPartial_zero hΦ]
  simp [cellB1, hv, r2c_fastPartial_zero (h1 _), r2c_fastPartial_zero hΦ, slowPartial]

theorem r2c_cellB2_zind (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    {Φ : Vec 2 → Vec 2 → E} (hΦ : R2ZInd Φ) : R2ZInd (cellB2 η G t Φ) := by
  intro X z z'
  have h2 : ∀ i j, R2ZInd (fun X' z' => G t X' i j • slowPartial j Φ X' z') := fun i j X' a b => by
    simp [r2c_slowPartial_zind hΦ j X' a b]
  simp only [cellB2, r2c_slowPartial_zind (h2 _ _) _ X z z']

theorem r2c_fieldCellMean_of_zind [CompleteSpace E] {Φ : Vec 2 → Vec 2 → E} (hΦ : R2ZInd Φ) (X z : Vec 2) :
    fieldCellMean (fun z' => Φ X z') = Φ X z := by
  have : (fun z' => Φ X z') = fun _ => Φ X z := funext fun z' => hΦ X z' z
  have hv : volume AVenhance.unitCube = 1 := by
    unfold AVenhance.unitCube
    rw [volume_pi, Measure.pi_pi]
    simp [Real.volume_Ioo]
  rw [fieldCellMean, this, setIntegral_const]
  simp [Measure.real, hv]

end AVRegularity.EntryTerminal.Ingredients.Recon.R2Core
end
end

section
/-! # Lift-sequence core, restriction of lift sequences

A cell field inverse on `[t₀,t₁]` restricts to a sub-interval `[a,b]` once its trace at `a` is the
new initial state; a lift sequence restricts to the right unchanged, and to the left when all its
positive lifts vanish at the new start. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution

namespace AVRegularity.EntryTerminal.Ingredients.Recon.R2Core

/-- The restriction of a cell field inverse to a sub-interval, with a new initial state. -/
theorem r2c_cellFieldInverse_restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {sZ : ℕ} {t₀ t₁ a b : ℝ} {c₀ c₀' : Vec 2 → E} {g c : ℝ → Vec 2 → E}
    (hc : IsCellFieldInverse G v sZ t₀ t₁ c₀ g c) (ha : t₀ ≤ a) (hb : b ≤ t₁)
    (hinit : ∀ ℓ : E →L[ℝ] ℝ, cellValue (cellJetOfField ℓ c) a =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => ((ℓ (c₀' x) : ℝ) : ℂ))) :
    IsCellFieldInverse G v sZ a b c₀' g c := by
  have hsub : Set.Icc a b ⊆ Set.Icc t₀ t₁ := Set.Icc_subset_Icc ha hb
  refine ⟨fun t ht => hc.1 t ⟨ha.trans ht.1, ht.2.trans hb⟩, fun ℓ => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hc.2 ℓ
  refine ⟨cellSolution_restrict hsub Set.ordConnected_Icc h1,
    fun t ht => h2 t (hsub ht), hinit ℓ, ?_⟩
  exact lt_of_le_of_lt (AVRegularity.InitialLayer.cellEnergyNorm_mono hsub _) h4

section Seq

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

/-- A lift sequence restricts to a sub-interval with the same start. -/
theorem r2c_liftSequence_restrict_right {Q : LiftOperatorData ι h D} {sX sZ N H : ℕ}
    {t₀ b t₁ : ℝ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (hb : b ≤ t₁) :
    IsLiftSequence Q sX sZ t₀ b N H Cc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hC
  refine ⟨fun a₀ ha₀ t ht X z => h1 a₀ ha₀ t ⟨ht.1, ht.2.trans hb⟩ X z, h2, h3, h4, h5,
    fun hh hhH n m α v u t ht => h6 hh hhH n m α v u t ⟨ht.1, ht.2.trans hb⟩,
    fun hh hhH n hn1 hnN a₀ ha₀ X => ?_⟩
  exact r2c_cellFieldInverse_restrict (h7 hh hhH n hn1 hnN a₀ ha₀ X) le_rfl hb
    (fun ℓ => ((h7 hh hhH n hn1 hnN a₀ ha₀ X).2 ℓ).2.2.1)

/-- A lift sequence whose positive lifts vanish at `s` restarts at `s`. -/
theorem r2c_liftSequence_restart {Q : LiftOperatorData ι h D} {sX sZ N H : ℕ}
    {t₀ s b t₁ : ℝ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (hs : t₀ ≤ s) (hb : b ≤ t₁)
    (hz : ∀ hh ≤ H, ∀ n, 1 ≤ n → ∀ m (α : DerivativeWord2 m) X z v u,
      Cc hh n m α s X z v u = 0) :
    IsLiftSequence Q sX sZ s b N H Cc := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hC
  refine ⟨fun a₀ ha₀ t ht X z => h1 a₀ ha₀ t ⟨hs.trans ht.1, ht.2.trans hb⟩ X z, h2, h3, h4, h5,
    fun hh hhH n m α v u t ht => h6 hh hhH n m α v u t ⟨hs.trans ht.1, ht.2.trans hb⟩,
    fun hh hhH n hn1 hnN a₀ ha₀ X => ?_⟩
  refine r2c_cellFieldInverse_restrict (h7 hh hhH n hn1 hnN a₀ ha₀ X) hs hb (fun ℓ => ?_)
  have e : cellValue (cellJetOfField ℓ (fun t z => liftApply n (Cc hh n) (fun _ => a₀) t X z)) s
      = fun x => ((ℓ (0 : ∀ i, h i) : ℝ) : ℂ) := by
    funext x
    have : liftApply n (Cc hh n) (fun _ => a₀) s X x = 0 := by
      funext v
      simp [liftApply, hz hh hhH n hn1]
    simp [cellValue, cellJetOfField, valueIndex2, valueIndex, this]
  exact Filter.EventuallyEq.of_eq e

end Seq

end AVRegularity.EntryTerminal.Ingredients.Recon.R2Core
end
end
end

section
section
/-! # Lift-sequence core (a): positive lifts started at zero stay zero

Comparison sequence `Cc'` (the order-`0` entries of `Cc`, all positive lifts zero). On `[t₀,s]` it is
a lift sequence: the centred source of every positive lift vanishes (everything is independent of the
fast variable), so the zero field is its cell inverse. Uniqueness identifies `Cc` with `Cc'`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution

namespace AVRegularity.EntryTerminal.Ingredients.Recon.R2Core

section Cell

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The zero field is the cell inverse of a source vanishing on the window. -/
theorem r2c_cellFieldInverse_zero_of_source {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {sZ : ℕ} {a b : ℝ} (hab : a ≤ b) {g : ℝ → Vec 2 → E}
    (hg : ∀ t ∈ Set.Icc a b, ∀ z, g t z = 0) :
    IsCellFieldInverse G v sZ a b (fun _ => 0) g (fun _ _ => 0) := by
  obtain ⟨h1, h2⟩ := AVRegularity.CycleComparison.Lift.cellFieldInverse_zero_field
    (E := E) G v sZ a b hab
  refine ⟨h1, fun ℓ => ?_⟩
  obtain ⟨s1, s2, s3, s4⟩ := h2 ℓ
  refine ⟨cellSolution_source_congr_sections (Set.Icc a b) _ _ _ _ _ _ ?_ ?_ s1, s2, s3, s4⟩
  · refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun r hr => ?_)
    exact Filter.EventuallyEq.of_eq (funext fun x => by simp [hg r hr x])
  · exact Filter.Eventually.of_forall fun r => Filter.EventuallyEq.rfl

end Cell

section Seq

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

/-- The comparison sequence: the order-`0` entries of `Cc`, all positive lifts zero. -/
def r2cCc' (Cc : ℕ → ℕ → LiftCoeff ι h) : ℕ → ℕ → LiftCoeff ι h :=
  fun hh n => if n = 0 then Cc hh 0 else 0

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem r2cCc'_pos (Cc : ℕ → ℕ → LiftCoeff ι h) (hh : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    r2cCc' Cc hh n = 0 := by
  simp [r2cCc', show n ≠ 0 by omega]

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem r2c_liftApply_zero (n : ℕ) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) :
    liftApply n (0 : LiftCoeff ι h) a t = 0 := by
  funext X z v
  simp [liftApply]

theorem r2c_zind_apply {Q : LiftOperatorData ι h D} {sX sZ N H : ℕ} {t₀ t₁ : ℝ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {hh : ℕ} (hhH : hh ≤ H)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) {a₀ : Vec 2 → ∀ i, h i} (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀)
    (k : ℕ) : R2ZInd (liftApply k (r2cCc' Cc hh k) (fun _ => a₀) t) := by
  by_cases hk : k = 0
  · subst hk
    by_cases hh0 : hh = 0
    · subst hh0
      intro X z z'
      have e : r2cCc' Cc 0 0 = Cc 0 0 := by simp [r2cCc']
      rw [e, hC.1 a₀ ha₀ t ht X z, hC.1 a₀ ha₀ t ht X z']
    · intro X z z'
      have e : r2cCc' Cc hh 0 = Cc hh 0 := by simp [r2cCc']
      have hz : liftApply 0 (Cc hh 0) (fun _ => a₀) t = 0 := by
        funext X z v
        simp [liftApply, hC.2.1 hh (by omega) hhH]
      rw [e, hz]; rfl
  · rw [r2cCc'_pos Cc hh (by omega), r2c_liftApply_zero]
    intro X z z'; rfl


theorem r2c_liftA_zind {Q : LiftOperatorData ι h D} {sX sZ N H : ℕ} {t₀ t₁ : ℝ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {hh : ℕ} (hhH : hh ≤ H)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) (hv : ∀ z, Q.v t z = 0)
    (hedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    {a₀ : Vec 2 → ∀ i, h i} (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀) (n : ℕ) :
    R2ZInd (liftA Q (r2cCc' Cc) (fun _ => a₀) hh n t) := by
  intro X z z'
  unfold liftA
  have hB1 := r2c_cellB1_zind Q.η Q.G Q.v t hv (r2c_zind_apply hC hhH ht ha₀ (n - 1)) X z z'
  have hB2 : (if 2 ≤ n then cellB2 Q.η Q.G t
        (liftApply (n - 2) (r2cCc' Cc hh (n - 2)) (fun _ => a₀) t) X z else 0) =
      (if 2 ≤ n then cellB2 Q.η Q.G t
        (liftApply (n - 2) (r2cCc' Cc hh (n - 2)) (fun _ => a₀) t) X z' else 0) := by
    split_ifs
    · exact r2c_cellB2_zind Q.η Q.G t (r2c_zind_apply hC hhH ht ha₀ (n - 2)) X z z'
    · rfl
  have hS : (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
        sourceCoeff Q.edge Q.η j t (liftApply (n - j) (r2cCc' Cc (hh - 1) (n - j))
          (fun _ => a₀) t) X z) =
      (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
        sourceCoeff Q.edge Q.η j t (liftApply (n - j) (r2cCc' Cc (hh - 1) (n - j))
          (fun _ => a₀) t) X z') := by
    split_ifs
    · rfl
    · refine Finset.sum_congr rfl fun j _ => ?_
      exact r2c_sourceCoeff_zind Q.edge Q.η t j hedge
        (r2c_zind_apply hC (by omega) ht ha₀ (n - j)) X z z'
  rw [hB1, hB2, hS]

theorem r2c_source_zero {Q : LiftOperatorData ι h D} {sX sZ N H : ℕ} {t₀ t₁ : ℝ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {hh : ℕ} (hhH : hh ≤ H)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) (hv : ∀ z, Q.v t z = 0)
    (hedge : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    {a₀ : Vec 2 → ∀ i, h i} (ha₀ : ContDiff ℝ (⊤ : ℕ∞) a₀) (n : ℕ) (X z : Vec 2) :
    liftCellSource Q (r2cCc' Cc) (fun _ => a₀) hh n t X z = 0 := by
  have : CompleteSpace (∀ i, h i) := FiniteDimensional.complete ℝ _
  have hm : liftMean Q (r2cCc' Cc) (fun _ => a₀) hh n t X =
      liftA Q (r2cCc' Cc) (fun _ => a₀) hh n t X z :=
    r2c_fieldCellMean_of_zind (r2c_liftA_zind hC hhH ht hv hedge ha₀ n) X z
  unfold liftCellSource
  rw [hm, sub_self, neg_zero, zero_add]
  refine Finset.sum_eq_zero fun j hj => Finset.sum_eq_zero fun p _ => ?_
  rw [r2cCc'_pos Cc p.1 (Finset.mem_Icc.mp hj).1]
  have := congrFun (congrFun (r2c_liftApply_zero (h := h) j (liftMean Q (r2cCc' Cc) (fun _ => a₀) p.2 (n - j)) t) X) z
  exact this

end Seq

end AVRegularity.EntryTerminal.Ingredients.Recon.R2Core
end
end

section
/-! # Lift-sequence core (a): the quiet stretch keeps positive lifts at zero -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Ingredients.Recon

section Core

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

/-- **The core of lift-sequence core (a)**, with the ellipticity needed only on `[t₀, s]` and no drift bound
(the drift vanishes there). -/
theorem r2c_quietZero_core (Q : LiftOperatorData ι h D) (sX sZ N H : ℕ) (t₀ s t₁ : ℝ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (hs : t₀ ≤ s)
    (hs1 : s ≤ t₁) (hsymm : ∀ t X i j, Q.G t X i j = Q.G t X j i)
    (hell : ∃ lo hi : ℝ, 0 < lo ∧ ∀ t ∈ Set.Icc t₀ s, ∀ X (ξ : Vec 2),
      lo * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, Q.G t X i j * ξ i * ξ j ∧
        ∑ i, ∑ j, Q.G t X i j * ξ i * ξ j ≤ hi * ∑ i, ξ i ^ 2)
    (hv : ∀ t ∈ Set.Icc t₀ s, ∀ z, Q.v t z = 0)
    (hedge : ∀ t ∈ Set.Icc t₀ s, ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z z',
      γ.coeff α t X z = γ.coeff α t X z') :
    ∀ hh ≤ H, ∀ n, 1 ≤ n → ∀ m (α : DerivativeWord2 m), ∀ t ∈ Set.Icc t₀ s, ∀ X z v u,
      Cc hh n m α t X z v u = 0 := by
  intro hh hhH n hn m α t ht X z v u
  have hCs : IsLiftSequence Q sX sZ t₀ s N H Cc := R2Core.r2c_liftSequence_restrict_right hC hs1
  have hCc' : IsLiftSequence Q sX sZ t₀ s N H (R2Core.r2cCc' Cc) := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hC
    have hsub : ∀ t ∈ Set.Icc t₀ s, t ∈ Set.Icc t₀ t₁ := fun t ht => ⟨ht.1, ht.2.trans hs1⟩
    refine ⟨fun a₀ ha₀ t ht X z => ?_, fun hh hh1 hhH m α t X z v u => ?_,
      fun hh hhH n hnN m α t X z v u => ?_, fun hh hhH n m hnm α t X z v u => ?_,
      fun hh hhH n m α σ => ?_, fun hh hhH n m α v u t ht => ?_,
      fun hh hhH n hn1 hnN a₀ ha₀ X => ?_⟩
    · have e : R2Core.r2cCc' Cc 0 0 = Cc 0 0 := by simp [R2Core.r2cCc']
      rw [e]; exact h1 a₀ ha₀ t (hsub t ht) X z
    · have e : R2Core.r2cCc' Cc hh 0 = Cc hh 0 := by simp [R2Core.r2cCc']
      rw [e]; exact h2 hh hh1 hhH m α t X z v u
    · rw [R2Core.r2cCc'_pos Cc hh (by omega)]; rfl
    · by_cases hn0 : n = 0
      · subst hn0
        have e : R2Core.r2cCc' Cc hh 0 = Cc hh 0 := by simp [R2Core.r2cCc']
        rw [e]; exact h4 hh hhH 0 m hnm α t X z v u
      · rw [R2Core.r2cCc'_pos Cc hh (by omega)]; rfl
    · by_cases hn0 : n = 0
      · subst hn0
        have e : R2Core.r2cCc' Cc hh 0 = Cc hh 0 := by simp [R2Core.r2cCc']
        rw [e]; exact h5 hh hhH 0 m α σ
      · rw [R2Core.r2cCc'_pos Cc hh (by omega)]; rfl
    · by_cases hn0 : n = 0
      · subst hn0
        have e : R2Core.r2cCc' Cc hh 0 = Cc hh 0 := by simp [R2Core.r2cCc']
        rw [e]; exact h6 hh hhH 0 m α v u t (hsub t ht)
      · rw [R2Core.r2cCc'_pos Cc hh (by omega)]
        exact ⟨isBoxSmooth_zero sX sZ, fun X x n => rfl⟩
    · have hc : (fun t z => liftApply n (R2Core.r2cCc' Cc hh n) (fun _ => a₀) t X z) =
          fun _ _ => 0 := by
        funext t z
        rw [R2Core.r2cCc'_pos Cc hh hn1]
        exact congrFun (congrFun (R2Core.r2c_liftApply_zero (h := h) n (fun _ => a₀) t) X) z
      rw [hc]
      refine R2Core.r2c_cellFieldInverse_zero_of_source hs (fun t ht z => ?_)
      exact R2Core.r2c_source_zero (hC := ⟨h1, h2, h3, h4, h5, h6, h7⟩) hhH (hsub t ht)
        (hv t ht) (fun v u d γ hγ α X z z' => hedge t ht v u d γ hγ α X z z') ha₀ n X z
  obtain ⟨lo0, hi0, hlo0, hq0⟩ := hell
  have key := Uniqueness.lift_sequence_unique_window_on (Ω := Set.univ) Q t₀ s hs isOpen_univ
    (fun X _ => ⟨lo0, hi0, 0, Uniqueness.windowData_of_elliptic
      (fun t => Matrix.of (Q.G t X)) Q.v t₀ s lo0 hi0 0 (fun t => hsymm t X 0 1) hlo0
      (fun t ht ξ => hq0 t ht X ξ) (fun t ht z => by rw [hv t ht z]; simp)⟩)
    sX sZ N H Cc (R2Core.r2cCc' Cc) (Uniqueness.IsLiftSequence.toOn hCs _)
    (Uniqueness.IsLiftSequence.toOn hCc' _) hh hhH n m α t ht X (Set.mem_univ X) z v u
  rw [key, R2Core.r2cCc'_pos Cc hh hn]; rfl

end Core

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
end
