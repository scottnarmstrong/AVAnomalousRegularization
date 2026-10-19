-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Fast.Word
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom
public import AVRegularity.CycleComparison.Residual.QuietMean.EpsPoly
import AVRegularity.CycleComparison.Residual.CoarseFlux
public import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Word derivatives commute with continuous linear maps, and the sum over an orthonormal basis of
the squared coordinates of a field is its squared norm (Parseval), also for word derivatives. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Slow word derivatives commute with a continuous linear map. -/
theorem slowDerivs_clm (L : E →L[ℝ] F) : ∀ (l : List (Fin 2)) {φ : Vec 2 → Vec 2 → E},
    IsSlowSmooth (l.length + 1) φ →
      slowDerivs l (fun X z => L (φ X z)) = fun X z => L (slowDerivs l φ X z) := by
  intro l
  induction l with
  | nil => intro φ _; rfl
  | cons i l ih =>
      intro φ hφ
      rw [slowDerivs_cons, slowDerivs_cons]
      have hφ' : IsSlowSmooth (l.length + 1 + 1) φ := by simpa using hφ
      have hp : AVRegularity.slowPartial i (fun X z => L (φ X z)) =
          fun X z => L (AVRegularity.slowPartial i φ X z) := by
        funext X z
        unfold AVRegularity.slowPartial
        have hd : DifferentiableAt ℝ (fun X' => φ X' z) X :=
          ((hφ'.1 z).differentiable (by simp)) X
        rw [show (fun X' => L (φ X' z)) = L ∘ fun X' => φ X' z from rfl,
          fderiv_comp X L.differentiableAt hd, L.fderiv]
        rfl
      rw [hp]
      exact ih (hφ'.slowPartial i)

/-- Fast word derivatives commute with a continuous linear map. -/
theorem fastDerivs_clm (L : E →L[ℝ] F) : ∀ (m : List (Fin 2)) {g : Vec 2 → E},
    ContDiff ℝ (m.length : ℕ∞) g → fastDerivs m (fun z => L (g z)) = fun z => L (fastDerivs m g z) := by
  intro m
  induction m with
  | nil => intro g _; rfl
  | cons i m ih =>
      intro g hg
      rw [fastDerivs_cons, fastDerivs_cons]
      have hg' : ContDiff ℝ (((m.length : ℕ) : WithTop ℕ∞) + 1) g := by
        refine hg.of_le ?_
        simp only [List.length_cons]
        exact_mod_cast le_rfl
      have hp : (fun z => fderiv ℝ (fun z' => L (g z')) z (basisVec i)) =
          fun z => L (fderiv ℝ g z (basisVec i)) := by
        funext z
        have hd : DifferentiableAt ℝ g z := (hg'.differentiable (by simp)) z
        rw [show (fun z' => L (g z')) = L ∘ g from rfl, fderiv_comp z L.differentiableAt hd,
          L.fderiv]
        rfl
      rw [hp]
      exact ih (contDiff_fderiv_apply hg' i)

variable {κ : Type*} [Fintype κ] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Parseval for the complexified coordinates, with a common real factor. -/
theorem sum_enorm_sq_coord (b : OrthonormalBasis κ ℝ H) (K : ℝ) (w : H) :
    ∑ k, ‖((K * inner ℝ (b k) w : ℝ) : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (K ^ 2) * ‖w‖ₑ ^ 2 := by
  have h1 : ∀ k, ‖((K * inner ℝ (b k) w : ℝ) : ℂ)‖ₑ ^ 2 =
      ENNReal.ofReal (K ^ 2 * ‖inner ℝ (b k) w‖ ^ 2) := by
    intro k
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.norm_real, Real.norm_eq_abs,
      abs_mul, mul_pow, sq_abs, sq_abs, Real.norm_eq_abs, sq_abs]
  simp_rw [h1]
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity, ← Finset.mul_sum,
    b.sum_sq_norm_inner_right, ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
    ENNReal.ofReal_pow (norm_nonneg _)]

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Notation for the vector mixed jets used by the recursion: the cell `L²` norm, at one slow point,
of a fast word of a slow word of a field, and the block jets of the lift coefficients (a supremum
over degrees of words, word lengths, slow points and unit input vectors). -/

/-- The cell `L²` norm at the slow point `X` of the fast word `m` of the slow word `l` of `F`. -/
def vecJ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Vec 2 → Vec 2 → E) (X : Vec 2)
    (l m : List (Fin 2)) : ℝ≥0∞ :=
  eLpNorm (fun z => fastDerivs m (slowDerivs l F X) z) 2 (volume.restrict AVenhance.unitCube)

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The block jet of the coefficients of the level `(p, n')` at the time `σ`, in the block
`(w, u')`: slow words of length `≤ S`, fast words of length `≤ F`, all degrees `m ≤ n'` and words,
all slow points, unit input vectors. -/
def blkJ (Cc : ℕ → ℕ → LiftCoeff ι h) (p n' : ℕ) (σ : ℝ) (w u' : ι) (S F : ℕ) : ℝ≥0∞ :=
  ⨆ (m : Fin (n' + 1)) (α : DerivativeWord2 m) (l : {l : List (Fin 2) // l.length ≤ S})
    (mm : {mm : List (Fin 2) // mm.length ≤ F}) (X : Vec 2) (η : {η : h u' // ‖η‖ ≤ 1}),
    vecJ (fun X z => Cc p n' m α σ X z w u' η.1) X l.1 mm.1

theorem vecJ_le_blkJ (Cc : ℕ → ℕ → LiftCoeff ι h) (p n' : ℕ) (σ : ℝ) (w u' : ι) (S F : ℕ)
    {m : ℕ} (hm : m ≤ n') (α : DerivativeWord2 m) (l mm : List (Fin 2)) (hl : l.length ≤ S)
    (hmm : mm.length ≤ F) (X : Vec 2) (η : h u') (hη : ‖η‖ ≤ 1) :
    vecJ (fun X z => Cc p n' m α σ X z w u' η) X l mm ≤ blkJ Cc p n' σ w u' S F := by
  unfold blkJ
  refine le_iSup_of_le (⟨m, by omega⟩ : Fin (n' + 1)) ?_
  refine le_iSup_of_le α ?_
  refine le_iSup_of_le ⟨l, hl⟩ ?_
  refine le_iSup_of_le ⟨mm, hmm⟩ ?_
  refine le_iSup_of_le X ?_
  exact le_iSup_of_le ⟨η, hη⟩ le_rfl

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.QuietDecay

/-! Good and centred lifts of a lift sequence from an arbitrary entrance: the cell mean of a cell
field inverse is zero whatever its initial value, so the lifts of an `IsLiftSequenceFrom` are good
fields, centred for `n ≥ 1`. -/

section
open AVRegularity

theorem fieldCellMean_eq_zero_of_IsCellFieldInverse_from
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (t₀ t₁ : ℝ) (c₀ : Vec 2 → E) (g c : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse (fun t => G t) v sZ t₀ t₁ c₀ g c)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    fieldCellMean (c t) = 0 := by
  have hcont : Continuous (c t) := (hc.1 t ht).continuous
  have hint : IntegrableOn (c t) (AVenhance.Infra.Torus.unitCell 2) :=
    AVenhance.Infra.Torus.Calculus.continuous_integrableOn_unitCell hcont
  let m : E := ∫ z in AVenhance.Infra.Torus.unitCell 2, c t z
  have hdual : ∀ ℓ : E →L[ℝ] ℝ, ℓ m = 0 := by
    intro ℓ
    have hmean := (hc.2 ℓ).2.1 t ht
    have hmeanCube :
        (∫ z in AVenhance.unitCube, ((ℓ (c t z) : ℝ) : ℂ)) = 0 := by
      simpa [cellMean, cellValue, cellJetOfField, valueIndex2, valueIndex] using hmean
    have hmeanCell :
        (∫ z in AVenhance.Infra.Torus.unitCell 2,
          ((ℓ (c t z) : ℝ) : ℂ)) = 0 := by
      rw [AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
      exact hmeanCube
    have hreal : (∫ z in AVenhance.Infra.Torus.unitCell 2, ℓ (c t z)) = 0 := by
      apply Complex.ofReal_injective
      calc
        ((∫ z in AVenhance.Infra.Torus.unitCell 2, ℓ (c t z) : ℝ) : ℂ) =
            ∫ z in AVenhance.Infra.Torus.unitCell 2, ((ℓ (c t z) : ℝ) : ℂ) := by
          simp only [integral_complex_ofReal]
        _ = 0 := hmeanCell
    have hmap := ℓ.integral_comp_comm hint
    change ℓ (∫ z in AVenhance.Infra.Torus.unitCell 2, c t z) = 0
    rw [← hmap]
    exact hreal
  have hm : m = 0 := SeparatingDual.eq_zero_of_forall_dual_eq_zero hdual
  change (∫ z in AVenhance.unitCube, c t z) = 0
  rw [← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
  exact hm

section LiftSeqFrom
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftApply_fieldCellMean_eq_zero_from [∀ i, CompleteSpace (h i)]
    (Q : LiftOperatorData ι h D) {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc)
    {hh : ℕ} (hhh : hh ≤ H) {n : ℕ} (hn : 1 ≤ n) (hN : n ≤ N)
    {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ (⊤ : ℕ∞) a₀)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) (X : Vec 2) :
    fieldCellMean (fun z => liftApply n (Cc hh n) (fun _ => a₀) t X z) = 0 := by
  rcases hseq with ⟨_, _, _, _, _, _, hinv⟩
  have hfield := hinv hh hhh n hn hN a₀ ha X
  exact fieldCellMean_eq_zero_of_IsCellFieldInverse_from
    (fun s => Matrix.of (Q.G s X)) Q.v sZ t₀ t₁ _
    (fun s z => liftCellSource Q Cc (fun _ => a₀) hh n s X z)
    (fun s z => liftApply n (Cc hh n) (fun _ => a₀) s X z) hfield ht

theorem liftApply_goodField_of_seqFrom (Q : LiftOperatorData ι h D) {sX sZ : ℕ} {t₀ t₁ : ℝ}
    {N H : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc)
    {r : ℕ} (hr : r ≤ sX) (hr' : r ≤ sZ) {hh : ℕ} (hhh : hh ≤ H) (n : ℕ)
    {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ (⊤ : ℕ∞) a₀) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    GoodField r (liftApply n (Cc hh n) (fun _ => a₀) t) := by
  obtain ⟨_, _, _, _, _, h6, _⟩ := hseq
  exact liftApply_goodField _ a₀ ha n r t fun m α v u =>
    ⟨((h6 hh hhh n m α v u t ht).1).mono hr hr', (h6 hh hhh n m α v u t ht).2⟩

theorem liftApply_centField_of_seqFrom [∀ i, CompleteSpace (h i)] (Q : LiftOperatorData ι h D)
    {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc)
    {r : ℕ} (hr : r ≤ sX) (hr' : r ≤ sZ) {hh : ℕ} (hhh : hh ≤ H) {n : ℕ} (hn : 1 ≤ n ∨ 1 ≤ hh)
    {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ (⊤ : ℕ∞) a₀) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    CoefField True r (liftApply n (Cc hh n) (fun _ => a₀) t) := by
  have hgood := liftApply_goodField_of_seqFrom Q hseq hr hr' hhh n ha ht
  by_cases hz : n = 0
  · subst hz
    have h2 : ∀ m α X z v u, Cc hh 0 m α t X z v u = 0 := by
      have := hseq.2.1 hh (by omega) hhh
      exact fun m α X z v u => this m α t X z v u
    rw [liftApply_eq_zero _ _ 0 t h2]
    exact CoefField.zero
  · refine ⟨hgood, fun _ X => ?_⟩
    by_cases hN : n ≤ N
    · exact liftApply_fieldCellMean_eq_zero_from Q hseq hhh (by omega) hN ha ht X
    · have h3 : ∀ m α X z v u, Cc hh n m α t X z v u = 0 := fun m α X z v u =>
        hseq.2.2.1 hh hhh n (by omega) m α t X z v u
      rw [liftApply_eq_zero _ _ n t h3]
      exact fieldCellMean_zero

end LiftSeqFrom
end

/-! The quiet decomposition of the recursion source `A_n^{(hh)} = lead + fast` at a quiet time:
`lead` is centred (the terms built from lifts of positive degree) and `fast` is fast independent
(the terms built from the degree-zero lifts). -/

section
open AVRegularity

section Defs
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The right side of the quiet-mean formula. -/
def quietMeanOp (Q : LiftOperatorData ι h D) (a₀ : Vec 2 → ∀ i, h i) (p2 n' : ℕ) (s : ℝ)
    (X' : Vec 2) : ∀ i, h i :=
  if p2 = 0 then (if n' = 2 then cellB2 Q.η Q.G s (fun X'' _ => a₀ X'') X' 0 else 0)
  else if p2 = 1 then -sourceCoeff Q.edge Q.η n' s (fun X'' _ => a₀ X'') X' 0 else 0

/-- The exact quiet decomposition of the cell source of the lift. -/
def quietSource (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a₀ : Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) : Vec 2 → Vec 2 → ∀ i, h i :=
  fun X z =>
    -(if 2 ≤ n then cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z
        else 0)
      - (if 3 ≤ n then cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z
        else 0)
      + (if hh = 0 then 0 else ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n),
          sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a₀) t) X z)
      + ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
          liftApply j (Cc p.1 j) (fun s X' => quietMeanOp Q a₀ p.2 (n - j) s X') t X z

/-- The centred part of the recursion source. -/
def quietLead (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a₀ : Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) : Vec 2 → Vec 2 → ∀ i, h i :=
  fun X z =>
    (if 2 ≤ n then cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z
        else 0)
      + (if 3 ≤ n then cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z
        else 0)
      - (if hh = 0 then 0 else ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n),
          sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a₀) t) X z)

/-- The fast independent part of the recursion source. -/
def quietFast (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a₀ : Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) : Vec 2 → Vec 2 → ∀ i, h i :=
  fun X z =>
    (if n = 1 then cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z
        else 0)
      + (if n = 2 then cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z
        else 0)
      - (if hh ≠ 0 ∧ n ≤ D then sourceCoeff Q.edge Q.η n t
          (liftApply (n - n) (Cc (hh - 1) (n - n)) (fun _ => a₀) t) X z else 0)

theorem quietSource_eq_neg_lead_add (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a₀ : Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) (X z : Vec 2) :
    quietSource Q Cc a₀ hh n t X z = -quietLead Q Cc a₀ hh n t X z
      + ∑ j ∈ Finset.Icc 1 (n - 2), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
          liftApply j (Cc p.1 j) (fun s X' => quietMeanOp Q a₀ p.2 (n - j) s X') t X z := by
  simp only [quietSource, quietLead]
  abel

theorem sum_range_min_split {E : Type*} [AddCommMonoid E] (D n : ℕ) (f : ℕ → E) :
    ∑ j ∈ Finset.range (min D n + 1), f j =
      ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n), f j + (if n ≤ D then f n else 0) := by
  by_cases hn : n ≤ D
  · rw [min_eq_right hn, Finset.sum_range_succ]
    simp only [hn, ↓reduceIte]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j; simp only [Finset.mem_range, Finset.mem_filter]; omega
  · simp only [hn, ↓reduceIte, add_zero]
    refine (Finset.sum_congr ?_ fun _ _ => rfl)
    rw [Finset.filter_true_of_mem]
    intro j hj
    have := Finset.mem_range.mp hj
    have h2 : min D n ≤ D := min_le_left _ _
    omega

theorem liftA_eq_quietLead_add (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a₀ : Vec 2 → ∀ i, h i) (t : ℝ) {hh n : ℕ} (hn : 1 ≤ n) (X z : Vec 2) :
    liftA Q Cc (fun _ => a₀) hh n t X z = quietLead Q Cc a₀ hh n t X z
      + quietFast Q Cc a₀ hh n t X z := by
  simp only [liftA, quietLead, quietFast]
  rw [sum_range_min_split D n]
  by_cases h1 : n = 1
  · subst h1
    by_cases h0 : hh = 0
    · simp [h0]
    · simp [h0]; abel
  · by_cases h2 : n = 2
    · subst h2
      by_cases h0 : hh = 0
      · simp [h0]
      · simp [h0]; abel
    · have h3 : 3 ≤ n := by omega
      have h4 : 2 ≤ n := by omega
      by_cases h0 : hh = 0
      · simp [h0, h1, h2, h3, h4]
      · simp [h0, h1, h2, h3, h4]; abel

end Defs

section Pieces
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem FastIndep.zero : FastIndep (fun (_ _ : Vec 2) => (0 : E)) := fun _ _ _ => rfl

omit [NormedSpace ℝ E] in
theorem FastIndep.add' {Ψ Φ : Vec 2 → Vec 2 → E} (hΨ : FastIndep Ψ) (hΦ : FastIndep Φ) :
    FastIndep (fun X z => Ψ X z + Φ X z) := fun X z z' => by simp only [hΨ X z z', hΦ X z z']

omit [NormedSpace ℝ E] in
theorem FastIndep.neg' {Ψ : Vec 2 → Vec 2 → E} (hΨ : FastIndep Ψ) :
    FastIndep (fun X z => -Ψ X z) := fun X z z' => by simp only [hΨ X z z']

omit [NormedSpace ℝ E] in
theorem FastIndep.ite' (c : Prop) [Decidable c] {Ψ : Vec 2 → Vec 2 → E} (hΨ : c → FastIndep Ψ) :
    FastIndep (fun X z => if c then Ψ X z else 0) := by
  by_cases hc : c
  · simpa only [hc, ↓reduceIte] using hΨ hc
  · simpa only [hc, ↓reduceIte] using (FastIndep.zero (E := E))

theorem cellB1_eq_zero_of_fastIndep (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (hquiet : ∀ z k, Real.sqrt η * v t z k = 0)
    {Φ : Vec 2 → Vec 2 → E} (hΦ : FastIndep Φ) : cellB1 η G v t Φ = fun _ _ => 0 := by
  funext X z
  have h1 : ∀ j : Fin 2, FastIndep (slowPartial j Φ) := fun j X a b => hΦ.slowPartial j X a b
  simp only [cellB1, hquiet, zero_smul, Finset.sum_const_zero, zero_sub]
  have e1 : ∀ i j : Fin 2, fastPartial i (slowPartial j Φ) X z = 0 := fun i j =>
    (h1 j).fastPartial i X z
  have e2 : ∀ j : Fin 2, fastPartial j Φ = fun _ _ => 0 := fun j => by
    funext X' z'; exact hΦ.fastPartial j X' z'
  simp only [e1, e2, smul_zero, slowPartial_zero, zero_add, Finset.sum_const_zero, neg_zero]

end Pieces

theorem CoefField.congr_fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : Prop}
    {r : ℕ} {Φ Ψ : Vec 2 → Vec 2 → E} (h : ∀ X z, Φ X z = Ψ X z) (hΨ : CoefField c r Ψ) :
    CoefField c r Φ := by
  have : Φ = Ψ := funext fun X => funext fun z => h X z
  subst this; exact hΨ

section Facts
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (a₀ : Vec 2 → ∀ i, h i)
  (t : ℝ) (H : ℕ)

/-- The analytic facts about the lifts at a quiet time that the decomposition uses. -/
structure QuietFacts : Prop where
  D_ge : 2 ≤ D
  G_smooth : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => Q.G t X i j)
  drift : ∀ z k, Real.sqrt Q.η * Q.v t z k = 0
  edge_quiet : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z'
  edge_smooth : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
    ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z)
  good : ∀ g ≤ H, ∀ m, GoodField 2 (liftApply m (Cc g m) (fun _ => a₀) t)
  cent : ∀ g ≤ H, ∀ m, (1 ≤ m ∨ 1 ≤ g) →
    CoefField True D (liftApply m (Cc g m) (fun _ => a₀) t)
  fast0 : ∀ g ≤ H, FastIndep (liftApply 0 (Cc g 0) (fun _ => a₀) t)

variable {Q Cc a₀ t H} {hh n : ℕ}

theorem QuietFacts.lead_centField (hf : QuietFacts Q Cc a₀ t H) (hhH : hh ≤ H) :
    CoefField True 0 (quietLead Q Cc a₀ hh n t) := by
  have t1 : CoefField True 0 (fun X z => if 2 ≤ n then cellB1 Q.η Q.G Q.v t
      (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z else 0) := by
    by_cases hn : 2 ≤ n
    · simpa only [hn, ↓reduceIte] using
        cellB1_centField Q.η Q.G Q.v t hf.G_smooth hf.drift (hf.good hh hhH (n - 1))
    · simpa only [hn, ↓reduceIte] using (CoefField.zero (c := True) (r := 0))
  have t2 : CoefField True 0 (fun X z => if 3 ≤ n then cellB2 Q.η Q.G t
      (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z else 0) := by
    by_cases hn : 3 ≤ n
    · simpa only [hn, ↓reduceIte] using cellB2_centField Q.η Q.G t hf.G_smooth
        ((hf.cent hh hhH (n - 2) (Or.inl (by omega))).mono hf.D_ge)
    · simpa only [hn, ↓reduceIte] using (CoefField.zero (c := True) (r := 0))
  have t3 : CoefField True 0 (fun X z => if hh = 0 then 0 else
      ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n), sourceCoeff Q.edge Q.η j t
        (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a₀) t) X z) := by
    by_cases hz : hh = 0
    · simpa only [hz, ↓reduceIte] using (CoefField.zero (c := True) (r := 0))
    · simp only [hz, ↓reduceIte]
      refine CoefField.sum _ fun j hj => ?_
      have hjn := (Finset.mem_filter.mp hj).2
      exact sourceCoeff_centField Q.edge (by have := hf.D_ge; omega) Q.η t hf.edge_quiet
        hf.edge_smooth (hf.cent (hh - 1) (by omega) (n - j) (Or.inl (by omega))) j
  refine CoefField.congr_fun (fun X z => ?_) ((t1.add t2).add t3.neg)
  simp only [quietLead, sub_eq_add_neg]

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem QuietFacts.fast_fastIndep (hf : QuietFacts Q Cc a₀ t H) (hhH : hh ≤ H) :
    FastIndep (quietFast Q Cc a₀ hh n t) := by
  have t1 : FastIndep (fun X z => if n = 1 then cellB1 Q.η Q.G Q.v t
      (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z else 0) := by
    refine FastIndep.ite' _ fun hn => ?_
    rw [show n - 1 = 0 by omega, cellB1_eq_zero_of_fastIndep _ _ _ t hf.drift (hf.fast0 hh hhH)]
    exact FastIndep.zero
  have t2 : FastIndep (fun X z => if n = 2 then cellB2 Q.η Q.G t
      (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z else 0) := by
    refine FastIndep.ite' _ fun hn => ?_
    rw [show n - 2 = 0 by omega]
    exact FastIndep.cellB2 _ _ t (hf.fast0 hh hhH)
  have t3 : FastIndep (fun X z => if hh ≠ 0 ∧ n ≤ D then sourceCoeff Q.edge Q.η n t
      (liftApply (n - n) (Cc (hh - 1) (n - n)) (fun _ => a₀) t) X z else 0) := by
    refine FastIndep.ite' _ fun hn => ?_
    rw [Nat.sub_self]
    exact sourceCoeff_fastIndep Q.edge Q.η t n hf.edge_quiet (hf.fast0 (hh - 1) (by omega))
  intro X z z'
  have key := (FastIndep.add' (FastIndep.add' t1 t2) (FastIndep.neg' t3)) X z z'
  simpa only [quietFast, sub_eq_add_neg] using key

end Facts
end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! The exact cell means of the lifts in a quiet gap for a lift sequence from an arbitrary
entrance (`IsLiftSequenceFrom`): `L_2^{(0)} = ℬ₂ I`, `L_n^{(1)} = -𝒮_n I`, all other means vanish
for `2 ≤ n ≤ N + D`, at quiet times, under `D ≤ max (k + 1) (L + 2)`. -/

open AVRegularity

theorem quiet_mean_from (N K k L D H : ℕ) (CG Cw : ℕ → ℝ)
    (Cj : ℕ → ℕ → ℝ) (hDsZ : D ≤ max (k + 1) (L + 2)) :
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
      (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
      IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
        IsLiftSequenceFrom Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
      ∀ S : Set ℝ, S ⊆ Set.Icc t₀ t₁ →
        IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S →
      ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ hh, hh ≤ H →
        ∀ n, 2 ≤ n → n ≤ N + D → ∀ t ∈ S, ∀ X,
          liftMean Q Cc (fun _ => a₀) hh n t X
            = if hh = 0 then (if n = 2 then cellB2 Q.η Q.G t (fun X' _ => a₀ X') X 0 else 0)
              else if hh = 1 then -sourceCoeff Q.edge Q.η n t (fun X' _ => a₀ X') X 0
              else 0 := by
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ hset Cc hseq S hS hq a₀
    ha hh hhH n hn2 hnND t htS X
  have htI : t ∈ Set.Icc t₀ t₁ := hS htS
  have hD2 : 2 ≤ D := hset.D_ge
  have hN1 : 1 ≤ N := hset.N_ge
  have hsX : D ≤ K + D + 2 := by omega
  have hqs1 : 1 ≤ qs := by
    rw [hset.qs_eq]
    have : 0 < 4 * (H + 1) * (N + D) ^ 2 := by
      have : 0 < N + D := by omega
      positivity
    omega
  have hG : ∀ i j, ContDiff ℝ (1 : ℕ∞) (fun X => Q.G t X i j) := fun i j =>
    (hset.G_smooth t htI i j).of_le (by exact_mod_cast hqs1)
  have hcq : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z' :=
    fun v u d γ hγ α X z z' => hq.2 v u d γ hγ α t htS X z z'
  have hsm : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z) := fun v u d γ hγ α z =>
    ((hset.coeff_smooth v u d γ hγ α t htI).contDiff_slow z).of_le (by exact_mod_cast hqs1)
  have hdrift : ∀ z k, Real.sqrt Q.η * Q.v t z k = 0 := fun z k => by
    have := congrFun (hq.1 t htS z) k
    simpa using this
  have hgood : ∀ hh' ≤ H, ∀ m, GoodField 2 (liftApply m (Cc hh' m) (fun _ => a₀) t) :=
    fun hh' hh'H m => liftApply_goodField_of_seqFrom Q hseq (r := 2) (by omega) (by omega) hh'H m ha htI
  have hcent : ∀ hh' ≤ H, ∀ m, (1 ≤ m ∨ 1 ≤ hh') →
      CoefField True D (liftApply m (Cc hh' m) (fun _ => a₀) t) := fun hh' hh'H m hm =>
    liftApply_centField_of_seqFrom Q hseq hsX hDsZ hh'H hm ha htI
  have hbase : liftApply 0 (Cc 0 0) (fun _ => a₀) t = fun X' _ => a₀ X' := by
    funext X' z; exact hseq.1 a₀ ha t htI X' z
  have hfi0 : FastIndep (fun (X' : Vec 2) (_ : Vec 2) => a₀ X') := fun _ _ _ => rfl
  -- the three pieces
  have hB1 := cellB1_centField Q.η Q.G Q.v t hG hdrift (hgood hh hhH (n - 1))
  have claim2 : Continuous (fun z => cellB2 Q.η Q.G t
        (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z) ∧
      fieldCellMean (fun z => cellB2 Q.η Q.G t
        (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z) =
        (if hh = 0 ∧ n = 2 then cellB2 Q.η Q.G t (fun X' _ => a₀ X') X 0 else 0) := by
    by_cases hc : hh ≠ 0 ∨ 3 ≤ n
    · have hB2 := cellB2_centField Q.η Q.G t hG
        ((hcent hh hhH (n - 2) (by omega)).mono hD2)
      refine ⟨hB2.1.continuous_slice X, ?_⟩
      have hnot : ¬ (hh = 0 ∧ n = 2) := by omega
      rw [hB2.2 trivial X]
      simp [hnot]
    · have hh0 : hh = 0 := by omega
      have hn : n = 2 := by omega
      subst hh0 hn
      simp only [Nat.sub_self, hbase]
      have hfi := FastIndep.cellB2 Q.η Q.G t hfi0
      have hc : (fun z => cellB2 Q.η Q.G t (fun X' _ => a₀ X') X z) =
          fun _ => cellB2 Q.η Q.G t (fun X' _ => a₀ X') X 0 := funext fun z => hfi X z 0
      rw [hc]
      exact ⟨continuous_const, by simpa using fieldCellMean_const _⟩
  have claim3 : Continuous (fun z => if hh = 0 then (0 : ∀ i, h i) else
        ∑ j ∈ Finset.range (min D n + 1), sourceCoeff Q.edge Q.η j t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a₀) t) X z) ∧
      fieldCellMean (fun z => if hh = 0 then (0 : ∀ i, h i) else
        ∑ j ∈ Finset.range (min D n + 1), sourceCoeff Q.edge Q.η j t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a₀) t) X z) =
        (if hh = 1 then sourceCoeff Q.edge Q.η n t (fun X' _ => a₀ X') X 0 else 0) := by
    by_cases hh0 : hh = 0
    · subst hh0
      simp only [ite_true]
      exact ⟨continuous_const, by simpa using fieldCellMean_zero⟩
    · simp only [hh0, ite_false]
      have hsrc : ∀ j, ∀ {Φ : Vec 2 → Vec 2 → ∀ i, h i}, CoefField True D Φ →
          CoefField True 0 (sourceCoeff Q.edge Q.η j t Φ) := fun j Φ hΦ =>
        sourceCoeff_centField Q.edge (by omega) Q.η t hcq hsm hΦ j
      by_cases hA : 2 ≤ hh ∨ D < n
      · have hall : CoefField True 0 (fun X z => ∑ j ∈ Finset.range (min D n + 1),
            sourceCoeff Q.edge Q.η j t
              (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a₀) t) X z) :=
          CoefField.sum _ fun j hj => hsrc j (hcent (hh - 1) (by omega) (n - j) (by
            have := Finset.mem_range.mp hj
            have h1 : min D n ≤ D := min_le_left _ _
            have h2 : min D n ≤ n := min_le_right _ _
            omega))
        refine ⟨hall.1.continuous_slice X, ?_⟩
        rw [hall.2 trivial X]
        by_cases hh1 : hh = 1
        · have hDn : D < n := by omega
          simp only [hh1, ite_true]
          have := sourceCoeff_eq_zero_of_gt Q.edge (by omega) Q.η t hcq hsm ha hDn X 0
          rw [this]
        · simp [hh1]
      · have hh1 : hh = 1 := by omega
        have hnD : n ≤ D := by omega
        subst hh1
        simp only [ite_true]
        have hmin : min D n = n := min_eq_right hnD
        rw [hmin]
        have hsplit : (fun z => ∑ j ∈ Finset.range (n + 1), sourceCoeff Q.edge Q.η j t
            (liftApply (n - j) (Cc (1 - 1) (n - j)) (fun _ => a₀) t) X z) = fun z =>
            (∑ j ∈ Finset.range n, sourceCoeff Q.edge Q.η j t
              (liftApply (n - j) (Cc (1 - 1) (n - j)) (fun _ => a₀) t) X z) +
            sourceCoeff Q.edge Q.η n t (fun X' _ => a₀ X') X z := by
          funext z
          rw [Finset.sum_range_succ]
          simp only [Nat.sub_self, Nat.sub_self, hbase]
        have hlow : CoefField True 0 (fun X z => ∑ j ∈ Finset.range n, sourceCoeff Q.edge Q.η j t
            (liftApply (n - j) (Cc (1 - 1) (n - j)) (fun _ => a₀) t) X z) :=
          CoefField.sum _ fun j hj => hsrc j (hcent (1 - 1) (by omega) (n - j) (by
            have := Finset.mem_range.mp hj
            omega))
        have hfn : FastIndep (sourceCoeff Q.edge Q.η n t (fun (X' : Vec 2) (_ : Vec 2) => a₀ X')) :=
          sourceCoeff_fastIndep Q.edge Q.η t n hcq hfi0
        have hc : (fun z => sourceCoeff Q.edge Q.η n t (fun (X' : Vec 2) (_ : Vec 2) => a₀ X') X z) =
            fun _ => sourceCoeff Q.edge Q.η n t (fun (X' : Vec 2) (_ : Vec 2) => a₀ X') X 0 :=
          funext fun z => hfn X z 0
        have hcont : Continuous (fun z => sourceCoeff Q.edge Q.η n t
            (fun (X' : Vec 2) (_ : Vec 2) => a₀ X') X z) := by
          rw [hc]; exact continuous_const
        rw [hsplit]
        refine ⟨(hlow.1.continuous_slice X).add hcont, ?_⟩
        rw [fieldCellMean_add (hlow.1.continuous_slice X) hcont,
          hlow.2 trivial X, hc, fieldCellMean_const, zero_add]
  -- assemble
  have hmeanB1 : fieldCellMean (fun z => cellB1 Q.η Q.G Q.v t
      (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z) = 0 := hB1.2 trivial X
  have e : (fun z => liftA Q Cc (fun _ => a₀) hh n t X z) = fun z =>
      (cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z +
        cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z) -
      (if hh = 0 then (0 : ∀ i, h i) else
        ∑ j ∈ Finset.range (min D n + 1), sourceCoeff Q.edge Q.η j t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a₀) t) X z) := by
    funext z
    simp only [liftA, hn2, ite_true]
  have hmain : liftMean Q Cc (fun _ => a₀) hh n t X =
      fieldCellMean (fun z => liftA Q Cc (fun _ => a₀) hh n t X z) := rfl
  have hc1 : Continuous (fun z => cellB1 Q.η Q.G Q.v t
      (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z) := hB1.1.continuous_slice X
  have hc12 : Continuous (fun z => cellB1 Q.η Q.G Q.v t
      (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z +
      cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z) :=
    hc1.add claim2.1
  rw [hmain, e, fieldCellMean_sub hc12 claim3.1, fieldCellMean_add hc1 claim2.1, hmeanB1,
    claim2.2, claim3.2]
  by_cases hh0 : hh = 0
  · subst hh0
    by_cases hn : n = 2 <;> simp [hn]
  · by_cases hh1 : hh = 1
    · subst hh1
      simp
    · simp [hh0, hh1]

end AVRegularity.QuietDecay
end
