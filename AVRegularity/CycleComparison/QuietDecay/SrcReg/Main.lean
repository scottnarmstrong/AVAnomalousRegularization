-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Lift.Recentre
import AVRegularity.CycleComparison.QuietDecay.Partition.Main
import AVRegularity.CycleComparison.QuietDecay.Parts.EdgeD
public import AVRegularity.CycleComparison.QuietDecay.Source.BoundBox
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
import Mathlib.Data.Int.Star

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.QuietDecay

/-! Fast periodicity of the pieces of the quiet source: partial derivatives, the cell operators
`ℬ₁`, `ℬ₂`, lift actions, the covariant derivative words, the source flux and the source
coefficients all preserve `ℤ²`-periodicity in the fast variable. -/

open AVRegularity

section Basic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem sreg_per_add {f g : Vec 2 → E} (hf : AVenhance.IsZ2Periodic f)
    (hg : AVenhance.IsZ2Periodic g) : AVenhance.IsZ2Periodic (fun z => f z + g z) :=
  fun n x => by simp only [hf n x, hg n x]

omit [NormedSpace ℝ E] in
theorem sreg_per_sub {f g : Vec 2 → E} (hf : AVenhance.IsZ2Periodic f)
    (hg : AVenhance.IsZ2Periodic g) : AVenhance.IsZ2Periodic (fun z => f z - g z) :=
  fun n x => by simp only [hf n x, hg n x]

omit [NormedSpace ℝ E] in
theorem sreg_per_neg {f : Vec 2 → E} (hf : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (fun z => -f z) :=
  fun n x => by simp only [hf n x]

theorem sreg_per_smul (c : ℝ) {f : Vec 2 → E} (hf : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (fun z => c • f z) :=
  fun n x => by simp only [hf n x]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem sreg_per_const (e : E) : AVenhance.IsZ2Periodic (fun _ : Vec 2 => e) := fun _ _ => rfl

omit [NormedSpace ℝ E] in
theorem sreg_per_sum {κ : Type*} (s : Finset κ) {f : κ → Vec 2 → E}
    (hf : ∀ k ∈ s, AVenhance.IsZ2Periodic (f k)) :
    AVenhance.IsZ2Periodic (fun z => ∑ k ∈ s, f k z) :=
  fun n x => Finset.sum_congr rfl fun k hk => hf k hk n x

theorem sreg_per_slowPartial (i : Fin 2) {Φ : Vec 2 → Vec 2 → E}
    (hΦ : ∀ X, AVenhance.IsZ2Periodic (Φ X)) :
    ∀ X, AVenhance.IsZ2Periodic (slowPartial i Φ X) :=
  periodic_slowIter [i] Φ hΦ

theorem sreg_per_fastPartial (i : Fin 2) {Φ : Vec 2 → Vec 2 → E}
    (hΦ : ∀ X, AVenhance.IsZ2Periodic (Φ X)) :
    ∀ X, AVenhance.IsZ2Periodic (fastPartial i Φ X) :=
  periodic_fastIter [i] Φ hΦ

theorem sreg_per_cellB1 {η : ℝ} {G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t : ℝ} (hv : ∀ z, Real.sqrt η • v t z = 0) {Φ : Vec 2 → Vec 2 → E}
    (hΦ : ∀ X, AVenhance.IsZ2Periodic (Φ X)) :
    ∀ X, AVenhance.IsZ2Periodic (cellB1 η G v t Φ X) := by
  intro X
  rw [cellB1_eq_of_drift hv Φ]
  refine sreg_per_smul _ (sreg_per_sum _ fun i _ => sreg_per_sum _ fun j _ => sreg_per_add ?_ ?_)
  · exact sreg_per_smul _ (sreg_per_fastPartial i (sreg_per_slowPartial j hΦ) X)
  · exact sreg_per_slowPartial i (fun X' => sreg_per_smul _
      (sreg_per_fastPartial j hΦ X')) X

theorem sreg_per_cellB2 {η : ℝ} {G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} {t : ℝ}
    {Φ : Vec 2 → Vec 2 → E} (hΦ : ∀ X, AVenhance.IsZ2Periodic (Φ X)) :
    ∀ X, AVenhance.IsZ2Periodic (cellB2 η G t Φ X) := by
  intro X
  rw [cellB2_eq]
  refine sreg_per_smul _ (sreg_per_sum _ fun i _ => sreg_per_sum _ fun j _ => ?_)
  exact sreg_per_slowPartial i (fun X' => sreg_per_smul _ (sreg_per_slowPartial j hΦ X')) X

end Basic

section Lift
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sreg_per_liftApply (M : ℕ) (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (hc : ∀ m α X v u, AVenhance.IsZ2Periodic (fun z => c m α t X z v u)) (X : Vec 2) :
    AVenhance.IsZ2Periodic (liftApply M c a t X) := by
  intro n z
  funext v
  have hc' : ∀ m (α : DerivativeWord2 m) (X : Vec 2) (n : Fin 2 → ℤ) (z : Vec 2) (v u : ι),
      c m α t X (z + AVenhance.latticeShift n) v u = c m α t X z v u :=
    fun m α X n z v u => hc m α X v u n z
  simp only [liftApply, hc']

theorem sreg_per_dEps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η ε : ℝ) (i : Fin 2)
    {Ψ : Vec 2 → Vec 2 → E} (hΨ : ∀ X, AVenhance.IsZ2Periodic (Ψ X)) :
    ∀ X, AVenhance.IsZ2Periodic (dEps η ε i Ψ X) := fun X =>
  sreg_per_add (sreg_per_fastPartial i hΨ X) (sreg_per_smul _ (sreg_per_slowPartial i hΨ X))

theorem sreg_per_dEpsFold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η ε : ℝ)
    (l : List (Fin 2)) : ∀ {Ψ : Vec 2 → Vec 2 → E}, (∀ X, AVenhance.IsZ2Periodic (Ψ X)) →
      ∀ X, AVenhance.IsZ2Periodic (l.foldl (fun Ψ' i => dEps η ε i Ψ') Ψ X) := by
  induction l with
  | nil => intro Ψ hΨ; exact hΨ
  | cons i l ih => intro Ψ hΨ; exact ih (sreg_per_dEps η ε i hΨ)

theorem sreg_per_sourceOp (edge : ConstituentEdges D h) (η ε t : ℝ)
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : ∀ X, AVenhance.IsZ2Periodic (Φ X)) (X : Vec 2) :
    AVenhance.IsZ2Periodic (sourceOp edge η ε t Φ X) := by
  have hper : ∀ (d : ℕ) (u v : ι) (γ : Constituent d (h u) (h v)) α t' X (n : Fin 2 → ℤ) z,
      γ.coeff α t' X (z + AVenhance.latticeShift n) = γ.coeff α t' X z :=
    fun d u v γ α t' X n z => γ.periodic α t' X n z
  have hw : ∀ (m : ℕ) (α : DerivativeWord2 m) (X : Vec 2) (n : Fin 2 → ℤ) (z : Vec 2),
      dEpsWord η ε α Φ X (z + AVenhance.latticeShift n) = dEpsWord η ε α Φ X z :=
    fun m α X n z => sreg_per_dEpsFold η ε (List.ofFn α) hΦ X n z
  have hfl : ∀ k : Fin 2, ∀ X, AVenhance.IsZ2Periodic (sourceFlux edge η ε t Φ k X) := by
    intro k X n z
    funext v
    simp only [sourceFlux, hper, hw]
  exact sreg_per_sum (Finset.univ : Finset (Fin 2))
    (f := fun k z => dEps η ε k (sourceFlux edge η ε t Φ k) X z)
    fun k _ => sreg_per_dEps η ε k (hfl k) X

/-- The source coefficients preserve fast periodicity. -/
theorem sreg_per_sourceCoeff (edge : ConstituentEdges D h) (η t : ℝ) (j : ℕ)
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} (hΦ : ∀ X, AVenhance.IsZ2Periodic (Φ X)) (X : Vec 2) :
    AVenhance.IsZ2Periodic (sourceCoeff edge η j t Φ X) := by
  intro n z
  have e : (fun ε : ℝ => sourceOp edge η ε t Φ X (z + AVenhance.latticeShift n)) =
      fun ε => sourceOp edge η ε t Φ X z :=
    funext fun ε => sreg_per_sourceOp edge η ε t hΦ X n z
  simp only [sourceCoeff, e]

end Lift

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.QuietDecay

/-! Box smoothness and fast periodicity of the quiet source `quietSource` of a smooth test field,
at a quiet time of a window of the lift. Slow orders are `P + 1` and fast orders `F`; the premises
are `P + 1 + D ≤ K + D + 2` (slow room of the coefficients), `F + D ≤ max (k+1) (L+2)` (fast
room of the coefficients), and `P + N + 2 ≤ qs` (smoothness of the metric and the edge
coefficients). -/

section
open AVRegularity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem sreg_boxSmooth_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (sX sZ : ℕ) :
    IsBoxSmooth sX sZ (fun (_ _ : Vec 2) => (0 : E)) :=
  edge_isBoxSmooth_slowOnly (g := fun _ => (0 : E)) contDiff_const

omit [∀ i, CompleteSpace (h i)] in
/-- The lift action of a coefficient array of a lift sequence is box smooth. -/
theorem sreg_liftApply_box {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
    {sX sZ N H : ℕ} {t₀ t₁ : ℝ} (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc) {g : ℕ}
    (hg : g ≤ H) (M : ℕ) {pX pZ : ℕ} (hX : pX ≤ sX) (hZ : pZ ≤ sZ)
    (a : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (ht : t ∈ Icc t₀ t₁)
    (ha : ContDiff ℝ ((pX + M : ℕ) : ℕ∞) (a t)) :
    IsBoxSmooth pX pZ (liftApply M (Cc g M) a t) := by
  refine edge_isBoxSmooth_pi fun v => ?_
  exact Partition.isBoxSmooth_liftApply M pX pZ (Cc g M) a t
    (fun m α v u => ((hseq.2.2.2.2.2.1 g hg M m α v u t ht).1).mono hX hZ) ha v

omit [DecidableEq ι] [∀ i, CompleteSpace (h i)] in
/-- The coefficients of a lift action are fast periodic. -/
theorem sreg_liftApply_per {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
    {sX sZ N H : ℕ} {t₀ t₁ : ℝ} (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc) {g : ℕ}
    (hg : g ≤ H) (M : ℕ) (a : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (ht : t ∈ Icc t₀ t₁) (X : Vec 2) :
    AVenhance.IsZ2Periodic (liftApply M (Cc g M) a t X) :=
  sreg_per_liftApply M (Cc g M) a t
    (fun m α X v u => (hseq.2.2.2.2.2.1 g hg M m α v u t ht).2 X) X

omit [DecidableEq ι] in
/-- The quiet mean operator of a smooth test field is smooth to any order allowed by the metric
and the edge coefficients. -/
theorem sreg_quietMeanOp_contDiff (Q : LiftOperatorData ι h D) (t : ℝ) (hD : 2 ≤ D)
    (hquiet : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z z', γ.coeff α t X z = γ.coeff α t X z')
    {b : Vec 2 → ∀ i, h i} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (p2 n' r : ℕ)
    (hG : ∀ i j, ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun X => Q.G t X i j))
    (hE : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
      ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun X => γ.coeff α t X z)) :
    ContDiff ℝ (r : ℕ∞) (fun X' => quietMeanOp Q b p2 n' t X') := by
  unfold quietMeanOp
  by_cases h0 : p2 = 0
  · simp only [h0, ↓reduceIte]
    by_cases h2 : n' = 2
    · simp only [h2, ↓reduceIte]
      exact GoodField.contDiff_zero_slice (cellB2_goodField Q.η Q.G t (r := r) hG
        (slow_goodField hb (r + 2)))
    · simp only [h2, ↓reduceIte]; exact contDiff_const
  · simp only [h0, ↓reduceIte]
    by_cases h1 : p2 = 1
    · simp only [h1, ↓reduceIte]
      have := sourceCoeff_coefField_r (c := False) (r := r) Q.edge (by omega) Q.η t
        hquiet hE (Φ := fun X (_ : Vec 2) => b X) ⟨slow_goodField hb (r + D), fun hf => hf.elim⟩ n'
      exact (GoodField.contDiff_zero_slice this.1).neg
    · simp only [h1, ↓reduceIte]; exact contDiff_const

section Quiet

variable {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {H N K k L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {b : ι → ι → ℝ} {Θ : ℝ}
    {Cc : ℕ → ℕ → LiftCoeff ι h}

/-- **Box smoothness and periodicity of the quiet source.** -/
theorem sreg_quietSource_box
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    (hseq : IsLiftSequenceFrom Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc)
    {S : Set ℝ} (hS : S ⊆ Icc t₀ t₁)
    (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S) {P F : ℕ}
    (hP : P + 1 + D ≤ K + D + 2) (hF : F + D ≤ max (k + 1) (L + 2)) (hqs : P + N + 2 ≤ qs)
    {hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N)
    {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ (⊤ : ℕ∞) a₀) {t : ℝ} (htS : t ∈ S) :
    IsBoxSmooth (P + 1) F (quietSource Q Cc a₀ hh n t) ∧
      ∀ X, AVenhance.IsZ2Periodic (quietSource Q Cc a₀ hh n t X) := by
  have ht : t ∈ Icc t₀ t₁ := hS htS
  have hD2 := hset.D_ge
  have hN1 := hset.N_ge
  have hdrift : ∀ z, Real.sqrt Q.η • Q.v t z = 0 := fun z => hq.1 t htS z
  have hquiet : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z z',
      γ.coeff α t X z = γ.coeff α t X z' := fun v u d γ hγ α X z z' =>
    hq.2 v u d γ hγ α t htS X z z'
  have hG : ∀ r ≤ qs, ∀ i j, ContDiff ℝ ((r : ℕ) : ℕ∞) (fun X => Q.G t X i j) :=
    fun r hr i j => (hset.G_smooth t ht i j).of_le (by exact_mod_cast hr)
  have hE : ∀ r ≤ qs, ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
      ContDiff ℝ ((r : ℕ) : ℕ∞) (fun X => γ.coeff α t X z) := fun r hr v u d γ hγ α z =>
    (((hset.coeff_smooth v u d γ hγ α t ht).isSlowSmooth).1 z).of_le (by exact_mod_cast hr)
  have hao : ∀ r : ℕ, ContDiff ℝ (r : ℕ∞) a₀ := fun r => ha.of_le (by exact_mod_cast le_top)
  -- the four groups of terms
  have E1 : IsBoxSmooth (P + 1) F (fun X z => if 2 ≤ n then cellB1 Q.η Q.G Q.v t
      (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z else 0) ∧
      ∀ X, AVenhance.IsZ2Periodic (fun z => if 2 ≤ n then cellB1 Q.η Q.G Q.v t
        (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) t) X z else 0) := by
    by_cases hn : 2 ≤ n
    · simp only [hn, ↓reduceIte]
      refine ⟨metric_isBoxSmooth_cellB1 (p := P + 1) (q := F) ?_ hdrift
        (fun i j => hG (P + 1 + 1) (by omega) i j), sreg_per_cellB1 hdrift fun X =>
          sreg_liftApply_per hseq hhH (n - 1) _ ht X⟩
      exact sreg_liftApply_box hseq hhH (n - 1) (by omega) (by omega) _ ht (hao _)
    · simp only [hn, ↓reduceIte]
      exact ⟨sreg_boxSmooth_zero _ _, fun X => sreg_per_const 0⟩
  have E2 : IsBoxSmooth (P + 1) F (fun X z => if 3 ≤ n then cellB2 Q.η Q.G t
      (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z else 0) ∧
      ∀ X, AVenhance.IsZ2Periodic (fun z => if 3 ≤ n then cellB2 Q.η Q.G t
        (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) t) X z else 0) := by
    by_cases hn : 3 ≤ n
    · simp only [hn, ↓reduceIte]
      refine ⟨metric_isBoxSmooth_cellB2 (p := P + 1) (q := F) ?_
        (fun i j => hG (P + 1 + 1) (by omega) i j), sreg_per_cellB2 fun X =>
          sreg_liftApply_per hseq hhH (n - 2) _ ht X⟩
      exact sreg_liftApply_box hseq hhH (n - 2) (by omega) (by omega) _ ht (hao _)
    · simp only [hn, ↓reduceIte]
      exact ⟨sreg_boxSmooth_zero _ _, fun X => sreg_per_const 0⟩
  have E3 : IsBoxSmooth (P + 1) F (fun X z => if hh = 0 then 0 else
      ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n),
        sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a₀) t) X z) ∧
      ∀ X, AVenhance.IsZ2Periodic (fun z => if hh = 0 then 0 else
        ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n),
          sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j))
            (fun _ => a₀) t) X z) := by
    by_cases hz : hh = 0
    · simp only [hz, ↓reduceIte]
      exact ⟨sreg_boxSmooth_zero _ _, fun X => sreg_per_const 0⟩
    · simp only [hz, ↓reduceIte]
      refine ⟨IsBoxSmooth.sum _ fun j _ => ?_, fun X => sreg_per_sum _ fun j _ =>
        sreg_per_sourceCoeff Q.edge Q.η t j (fun X' =>
          sreg_liftApply_per hseq (by omega) (n - j) _ ht X') X⟩
      exact edge_isBoxSmooth_sourceCoeff Q.edge Q.η t hquiet
        (sreg_liftApply_box hseq (g := hh - 1) (by omega) (n - j) (pX := P + 1 + D)
          (pZ := F + D) hP hF _ ht (hao _)) j le_rfl le_rfl (by omega) (by omega)
        (fun v u d γ hγ α z => hE (P + 1 + 1) (by omega) v u d γ hγ α z)
  have E4 : IsBoxSmooth (P + 1) F (fun X z => ∑ j ∈ Finset.Icc 1 (n - 2),
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftApply j (Cc p.1 j) (fun s X' => quietMeanOp Q a₀ p.2 (n - j) s X') t X z) ∧
      ∀ X, AVenhance.IsZ2Periodic (fun z => ∑ j ∈ Finset.Icc 1 (n - 2),
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
          liftApply j (Cc p.1 j) (fun s X' => quietMeanOp Q a₀ p.2 (n - j) s X') t X z) := by
    refine ⟨IsBoxSmooth.sum _ fun j hj => IsBoxSmooth.sum _ fun p hp => ?_,
      fun X => sreg_per_sum _ fun j _ => sreg_per_sum _ fun p hp => ?_⟩
    · have hj := Finset.mem_Icc.mp hj
      have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      refine sreg_liftApply_box hseq (g := p.1) (by omega) j (by omega) (by omega) _ ht ?_
      exact sreg_quietMeanOp_contDiff Q t hD2 hquiet ha p.2 (n - j) (P + 1 + j)
        (fun i i' => hG _ (by omega) i i') (fun v u d γ hγ α z => hE _ (by omega) v u d γ hγ α z)
    · have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      exact sreg_liftApply_per hseq (g := p.1) (by omega) j _ ht X
  unfold quietSource
  exact ⟨(((E1.1.neg).sub E2.1).add E3.1).add E4.1, fun X =>
    sreg_per_add (sreg_per_add (sreg_per_sub (sreg_per_neg (E1.2 X)) (E2.2 X)) (E3.2 X)) (E4.2 X)⟩

end Quiet
end

/-! Joint time-cell measurability of the lift actions and of the coefficient blocks of a lift
sequence on a window where the drift vanishes: from the measurable representatives of the cell
solutions, finite-dimensional dual reduction, and the mixed partial words. -/

section
open AVRegularity

section Dual

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A map into a finite-dimensional space is a.e. strongly measurable if all its functionals are. -/
theorem sreg_aesm_of_dual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : α → E}
    (hf : ∀ ℓ : E →L[ℝ] ℝ, AEStronglyMeasurable (fun p => ℓ (f p)) μ) :
    AEStronglyMeasurable f μ := by
  let b := Module.finBasis ℝ E
  have e : f = fun p => ∑ i, (LinearMap.toContinuousLinearMap (b.coord i)) (f p) • b i := by
    funext p
    have h1 : ∀ i, (LinearMap.toContinuousLinearMap (b.coord i)) (f p) = b.repr (f p) i :=
      fun i => by simp [Module.Basis.coord_apply]
    simp only [h1]
    exact (b.sum_repr (f p)).symm
  rw [e]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hf _).smul_const _

/-- A map into a finite product is a.e. strongly measurable if its components are. -/
theorem sreg_aesm_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {f : α → ∀ i, h i}
    (hf : ∀ i, AEStronglyMeasurable (fun p => f p i) μ) : AEStronglyMeasurable f μ := by
  have e : f = fun p => ∑ i, ContinuousLinearMap.single ℝ h i (f p i) := by
    funext p
    simp only [ContinuousLinearMap.single_apply]
    exact (Finset.univ_sum_single (f p)).symm
  rw [e]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    (ContinuousLinearMap.single ℝ h i).continuous.comp_aestronglyMeasurable (hf i)

/-- A finite-dimensional linear map applied to a measurable vector, through a basis. -/
theorem sreg_aesm_clm_apply {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] {c : α → E →L[ℝ] E'}
    {w : α → E}
    (hc : ∀ x : E, AEStronglyMeasurable (fun p => c p x) μ)
    (hw : ∀ ℓ : E →L[ℝ] ℝ, AEStronglyMeasurable (fun p => ℓ (w p)) μ) :
    AEStronglyMeasurable (fun p => c p (w p)) μ := by
  let b := Module.finBasis ℝ E
  have e : (fun p => c p (w p)) = fun p => ∑ i,
      (LinearMap.toContinuousLinearMap (b.coord i)) (w p) • c p (b i) := by
    funext p
    have h1 : ∀ i, (LinearMap.toContinuousLinearMap (b.coord i)) (w p) = b.repr (w p) i :=
      fun i => by simp [Module.Basis.coord_apply]
    simp only [h1]
    conv_lhs => rw [← b.sum_repr (w p)]
    simp only [map_sum, map_smul]
  rw [e]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hw _).smul (hc _)

end Dual

section Mixed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {J : Set ℝ}
  {F : ℝ → Vec 2 → Vec 2 → E} {s : ℕ}

theorem sreg_per_mixed (w : List (Bool × Fin 2)) :
    ∀ {Φ : Vec 2 → Vec 2 → E}, (∀ X, AVenhance.IsZ2Periodic (Φ X)) →
      ∀ X, AVenhance.IsZ2Periodic (mixed w Φ X) := by
  induction w using List.reverseRecOn with
  | nil => intro Φ hΦ; exact hΦ
  | append_singleton w b ih =>
    intro Φ hΦ
    rw [mixed_append_single]
    unfold mixedStep
    cases b.1
    · exact periodic_fastIter [b.2] _ (ih hΦ)
    · exact periodic_slowIter [b.2] _ (ih hΦ)

/-- **Mixed words are a.e. strongly measurable** in time and cell. -/
theorem sreg_aesm_mixed (hJ : MeasurableSet J) (hF : ∀ t ∈ J, IsBoxSmooth s s (F t))
    (hper : ∀ t ∈ J, ∀ X, AVenhance.IsZ2Periodic (F t X))
    (hmeas : ∀ X, AEStronglyMeasurable (fun p : ℝ × Vec 2 => F p.1 X p.2) (timeCellMeasure J))
    (w : List (Bool × Fin 2)) (hw : w.length ≤ s) (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => mixed w (F p.1) X p.2) (timeCellMeasure J) := by
  induction w using List.reverseRecOn generalizing X with
  | nil => simpa [mixed_nil] using hmeas X
  | append_singleton w b ih =>
    simp only [List.length_append, List.length_singleton] at hw
    have ih' := fun X' => ih (by omega) X'
    have hbox : ∀ t ∈ J, IsBoxSmooth (s - w.length) (s - w.length) (mixed w (F t)) :=
      fun t ht => isBoxSmooth_mixed w (hF t ht) (by omega)
    obtain ⟨m, hm⟩ : ∃ m, s - w.length = m + 1 := ⟨s - w.length - 1, by omega⟩
    simp only [mixed_append_single, mixedStep]
    cases hb : b.1
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine aestronglyMeasurable_fastPartial hJ (F := fun t => mixed w (F t)) ih'
        (fun t ht => sreg_per_mixed w (hper t ht)) (fun t ht X' => ?_) b.2 X
      have h1 := (hbox t ht)
      rw [hm] at h1
      exact ((h1.1 X').differentiable (by exact_mod_cast Nat.succ_ne_zero m))
    · simp only [↓reduceIte]
      refine aestronglyMeasurable_slowPartial hJ (F := fun t => mixed w (F t)) ih'
        (fun t ht z => ?_) b.2 X
      have h1 := (hbox t ht)
      rw [hm] at h1
      exact (h1.contDiff_slow z).differentiable (by exact_mod_cast Nat.succ_ne_zero m)

end Mixed

section Lift

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

variable {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}

omit [DecidableEq ι] [∀ i, CompleteSpace (h i)] in
/-- The lift action of a coefficient array of a lift sequence on a smooth time-independent test
field is a.e. strongly measurable in time and cell on a window where the drift vanishes. -/
theorem sreg_aesm_liftApply {sX sZ N H : ℕ} {t₀ t₁ : ℝ}
    (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc) {hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n)
    (hnN : n ≤ N) {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ (⊤ : ℕ∞) a₀) {J : Set ℝ}
    (hJ : J ⊆ Icc t₀ t₁) (hJc : J.OrdConnected) (hv : ∀ t ∈ J, ∀ z, Q.v t z = 0) (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => liftApply n (Cc hh n) (fun _ => a₀) p.1 X p.2)
      (timeCellMeasure J) := by
  refine sreg_aesm_of_dual fun ℓ => ?_
  have hfam := isCellFam_liftFam hseq hhH hn1 hnN ℓ (test := fun _ => a₀) (fun _ => ha) hJ hJc hv
  have h4 : AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
      cellValue ((liftFam Q Cc hh n ℓ (fun _ => a₀)).D X) p.1 p.2) (timeCellMeasure J) :=
    (hfam X).2.2.2.1 (valueIndex2 1)
  have h5 := Complex.continuous_re.comp_aestronglyMeasurable h4
  refine h5.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [liftFam_value, Complex.ofReal_re]

omit [DecidableEq ι] [∀ i, CompleteSpace (h i)] in
/-- The same, for every degree `n ≤ N`, including `n = 0`, at times of the window. -/
theorem sreg_aesm_liftApply_le {sX sZ N H : ℕ} {t₀ t₁ : ℝ}
    (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc) {hh n : ℕ} (hhH : hh ≤ H)
    (hnN : n ≤ N) {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ (⊤ : ℕ∞) a₀) {J : Set ℝ}
    (hJm : MeasurableSet J) (hJ : J ⊆ Icc t₀ t₁) (hJc : J.OrdConnected)
    (hv : ∀ t ∈ J, ∀ z, Q.v t z = 0) (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => liftApply n (Cc hh n) (fun _ => a₀) p.1 X p.2)
      (timeCellMeasure J) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · refine (aestronglyMeasurable_const (b := if hh = 0 then a₀ X else 0)).congr ?_
    filter_upwards [ae_timeCell_fst_mem hJm] with p hp
    by_cases h0 : hh = 0
    · subst h0
      simp only [↓reduceIte]
      exact (hseq.1 a₀ ha p.1 (hJ hp) X p.2).symm
    · have h2 : ∀ m α X z v u, Cc hh 0 m α p.1 X z v u = 0 := fun m α X z v u =>
        hseq.2.1 hh (by omega) hhH m α p.1 X z v u
      simp only [h0, ↓reduceIte]
      rw [liftApply_eq_zero _ _ 0 p.1 h2]
  · exact sreg_aesm_liftApply hseq hhH hn1 hnN ha hJ hJc hv X

omit [∀ i, CompleteSpace (h i)] in
/-- **The coefficient blocks are a.e. strongly measurable** in time and cell. -/
theorem sreg_aesm_coeff {sX sZ N H : ℕ} {t₀ t₁ : ℝ}
    (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc) {g j : ℕ} (hg : g ≤ H) (hj1 : 1 ≤ j)
    (hjN : j ≤ N) {m : ℕ} (hm : m ≤ j) (α : DerivativeWord2 m) (v u : ι) (x : h u) {J : Set ℝ}
    (hJ : J ⊆ Icc t₀ t₁) (hJc : J.OrdConnected) (hv : ∀ t ∈ J, ∀ z, Q.v t z = 0) (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => Cc g j m α p.1 X p.2 v u x)
      (timeCellMeasure J) := by
  have hsym : LiftSymm (Cc g j) := fun m α σ => hseq.2.2.2.2.1 g hg j m α σ
  have h1 := sreg_aesm_liftApply hseq hg hj1 hjN (contDiff_blockTest u x α X) hJ hJc hv X
  have h2 := (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).continuous.comp_aestronglyMeasurable h1
  have h3 := h2.const_smul ((liftK α : ℝ)⁻¹)
  refine h3.congr (Filter.Eventually.of_forall fun p => ?_)
  have e := liftApply_blockTest hsym hm α v u x p.1 X p.2
  have hK : (liftK α : ℝ) ≠ 0 := by
    have := one_le_liftK α
    positivity
  show ((liftK α : ℝ)⁻¹) • liftApply j (Cc g j) (fun _ => blockTest u x α X) p.1 X p.2 v = _
  rw [e, blockF, smul_smul, inv_mul_cancel₀ hK, one_smul]

end Lift
end

/-! Joint time-cell measurability of the cell operators `ℬ₁` (at a quiet time), `ℬ₂`, of the source
coefficients `𝒮_j`, and of the quiet mean operator, applied to time-dependent box smooth fields. -/

section
open AVRegularity

theorem sreg_diff_of_contDiff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {n : ℕ} (hn : 1 ≤ n)
    (hf : ContDiff ℝ (n : ℕ∞) f) : Differentiable ℝ f :=
  hf.differentiable (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hn)

section Cell

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {J : Set ℝ} {η : ℝ}
  {G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} {Φ : ℝ → Vec 2 → Vec 2 → E}

/-- **Measurability of `ℬ₁`** at times where the drift vanishes. -/
theorem sreg_aesm_cellB1 (hJ : MeasurableSet J) {v : ℝ → Vec 2 → Vec 2}
    (hv : ∀ t ∈ J, ∀ z, Real.sqrt η • v t z = 0)
    (hGm : ∀ X i j, Measurable fun t => G t X i j)
    (hGs : ∀ t ∈ J, ∀ i j, ContDiff ℝ ((1 : ℕ) : ℕ∞) (fun X => G t X i j))
    (hΦ : ∀ t ∈ J, IsBoxSmooth 2 2 (Φ t)) (hper : ∀ t ∈ J, ∀ X, AVenhance.IsZ2Periodic (Φ t X))
    (hmeas : ∀ X, AEStronglyMeasurable (fun p : ℝ × Vec 2 => Φ p.1 X p.2) (timeCellMeasure J))
    (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => cellB1 η G v p.1 (Φ p.1) X p.2)
      (timeCellMeasure J) := by
  have hdΦ : ∀ t ∈ J, ∀ z, Differentiable ℝ (fun X' => Φ t X' z) := fun t ht z =>
    sreg_diff_of_contDiff (by norm_num) ((hΦ t ht).contDiff_slow z)
  have hdF : ∀ t ∈ J, ∀ X', Differentiable ℝ (Φ t X') := fun t ht X' =>
    sreg_diff_of_contDiff (by norm_num) ((hΦ t ht).1 X')
  have hS : ∀ j : Fin 2, ∀ X', AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => slowPartial j (Φ p.1) X' p.2) (timeCellMeasure J) := fun j X' =>
    aestronglyMeasurable_slowPartial hJ hmeas hdΦ j X'
  have hFa : ∀ j : Fin 2, ∀ X', AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => fastPartial j (Φ p.1) X' p.2) (timeCellMeasure J) := fun j X' =>
    aestronglyMeasurable_fastPartial hJ hmeas hper hdF j X'
  have hA : ∀ i j : Fin 2, AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
      G p.1 X i j • fastPartial i (slowPartial j (Φ p.1)) X p.2) (timeCellMeasure J) := by
    intro i j
    refine aestronglyMeasurable_smul_slow (g := fun t X => G t X i j)
      (F := fun t X' z' => fastPartial i (slowPartial j (Φ t)) X' z') X
      (hGm X i j).aestronglyMeasurable ?_
    refine aestronglyMeasurable_fastPartial hJ (F := fun t => slowPartial j (Φ t)) (hS j)
      (fun t ht => sreg_per_slowPartial j (hper t ht)) (fun t ht X' => ?_) i X
    have h1 : IsBoxSmooth (1 + 1) 2 (Φ t) := hΦ t ht
    exact sreg_diff_of_contDiff (by norm_num) ((h1.slowPartial j).1 X')
  have hB : ∀ i j : Fin 2, AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
      slowPartial i (fun X' z' => G p.1 X' i j • fastPartial j (Φ p.1) X' z') X p.2)
      (timeCellMeasure J) := by
    intro i j
    refine aestronglyMeasurable_slowPartial hJ (F := fun t X' z' => G t X' i j •
      fastPartial j (Φ t) X' z') (fun X' => aestronglyMeasurable_smul_slow (g := fun t X => G t X i j)
        (F := fun t X' z' => fastPartial j (Φ t) X' z') X' (hGm X' i j).aestronglyMeasurable (hFa j X')) (fun t ht z => ?_) i X
    have h1 : IsBoxSmooth (1 + 1) 2 (Φ t) := hΦ t ht
    have h2 : IsBoxSmooth 2 1 (fastPartial j (Φ t)) := h1.fastPartial j
    exact ((hGs t ht i j).differentiable (by norm_num)).smul
      (sreg_diff_of_contDiff (by norm_num) (h2.contDiff_slow z))
  have hsum : AEStronglyMeasurable (fun p : ℝ × Vec 2 => (-Real.sqrt η) • ∑ i : Fin 2, ∑ j : Fin 2,
      (G p.1 X i j • fastPartial i (slowPartial j (Φ p.1)) X p.2
        + slowPartial i (fun X' z' => G p.1 X' i j • fastPartial j (Φ p.1) X' z') X p.2))
      (timeCellMeasure J) :=
    (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hA i j).add (hB i j)).const_smul _
  refine hsum.congr ?_
  filter_upwards [ae_timeCell_fst_mem hJ] with p hp
  exact (congrFun (congrFun (cellB1_eq_of_drift (hv p.1 hp) (Φ p.1)) X) p.2).symm

/-- **Measurability of `ℬ₂`.** -/
theorem sreg_aesm_cellB2 (hJ : MeasurableSet J)
    (hGm : ∀ X i j, Measurable fun t => G t X i j)
    (hGs : ∀ t ∈ J, ∀ i j, ContDiff ℝ ((1 : ℕ) : ℕ∞) (fun X => G t X i j))
    (hΦ : ∀ t ∈ J, IsBoxSmooth 2 0 (Φ t))
    (hmeas : ∀ X, AEStronglyMeasurable (fun p : ℝ × Vec 2 => Φ p.1 X p.2) (timeCellMeasure J))
    (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => cellB2 η G p.1 (Φ p.1) X p.2)
      (timeCellMeasure J) := by
  have hdΦ : ∀ t ∈ J, ∀ z, Differentiable ℝ (fun X' => Φ t X' z) := fun t ht z =>
    sreg_diff_of_contDiff (by norm_num) ((hΦ t ht).contDiff_slow z)
  have hS : ∀ j : Fin 2, ∀ X', AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => slowPartial j (Φ p.1) X' p.2) (timeCellMeasure J) := fun j X' =>
    aestronglyMeasurable_slowPartial hJ hmeas hdΦ j X'
  have hB : ∀ i j : Fin 2, AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
      slowPartial i (fun X' z' => G p.1 X' i j • slowPartial j (Φ p.1) X' z') X p.2)
      (timeCellMeasure J) := by
    intro i j
    refine aestronglyMeasurable_slowPartial hJ (F := fun t X' z' => G t X' i j •
      slowPartial j (Φ t) X' z') (fun X' => aestronglyMeasurable_smul_slow (g := fun t X => G t X i j)
        (F := fun t X' z' => slowPartial j (Φ t) X' z') X' (hGm X' i j).aestronglyMeasurable (hS j X')) (fun t ht z => ?_) i X
    have h1 : IsBoxSmooth (1 + 1) 0 (Φ t) := hΦ t ht
    have h2 : IsBoxSmooth 1 0 (slowPartial j (Φ t)) := h1.slowPartial j
    exact ((hGs t ht i j).differentiable (by norm_num)).smul
      (sreg_diff_of_contDiff (by norm_num) (h2.contDiff_slow z))
  have hsum : AEStronglyMeasurable (fun p : ℝ × Vec 2 => (-η) • ∑ i : Fin 2, ∑ j : Fin 2,
      slowPartial i (fun X' z' => G p.1 X' i j • slowPartial j (Φ p.1) X' z') X p.2)
      (timeCellMeasure J) :=
    (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun j _ => hB i j).const_smul _
  refine hsum.congr (Filter.Eventually.of_forall fun p => ?_)
  exact (congrFun (congrFun (cellB2_eq (η := η) (G := G) (t := p.1) (Φ p.1)) X) p.2).symm

end Cell

section Source

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- **Measurability of the source coefficients** (all components at once). -/
theorem sreg_aesm_sourceCoeff {J : Set ℝ} (hJ : MeasurableSet J) (edge : ConstituentEdges D h)
    (η : ℝ)
    (hquiet : ∀ t ∈ J, ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z z',
      γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ t ∈ J, ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    (hcoef : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α Y, Measurable fun t => γ.coeff α t Y 0)
    {Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i} (hΦ : ∀ t ∈ J, IsBoxSmooth D D (Φ t))
    (hper : ∀ t ∈ J, ∀ X, AVenhance.IsZ2Periodic (Φ t X))
    (hmeas : ∀ X, AEStronglyMeasurable (fun p : ℝ × Vec 2 => Φ p.1 X p.2) (timeCellMeasure J))
    (j : ℕ) (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => sourceCoeff edge η j p.1 (Φ p.1) X p.2)
      (timeCellMeasure J) := by
  refine sreg_aesm_pi fun v => ?_
  refine aesm_sourceCoeff_time_box edge η (ae_timeCell_fst_mem hJ) hquiet hsm hcoef hΦ le_rfl le_rfl
    (fun u w hw X' => ?_) j X v
  refine sreg_aesm_mixed (F := fun t X' z' => Φ t X' z' u) hJ
    (fun t ht => (hΦ t ht).map_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) u))
    (fun t ht X'' n z => by simp only [hper t ht X'' n z]) (fun X'' => ?_) w hw X'
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := h) u).continuous.comp_aestronglyMeasurable
    (hmeas X'')

variable {Q : LiftOperatorData ι h D}

/-- **Measurability of the quiet mean operator** of a smooth test field in time. -/
theorem sreg_aesm_quietMeanOp {J : Set ℝ} (hJ : MeasurableSet J)
    (hGm : ∀ X i j, Measurable fun t => Q.G t X i j)
    (hGs : ∀ t ∈ J, ∀ i j, ContDiff ℝ ((1 : ℕ) : ℕ∞) (fun X => Q.G t X i j))
    (hquiet : ∀ t ∈ J, ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z z',
      γ.coeff α t X z = γ.coeff α t X z')
    (hsm : ∀ t ∈ J, ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
      ContDiff ℝ (1 : ℕ∞) (fun X => γ.coeff α t X z))
    (hcoef : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α Y, Measurable fun t => γ.coeff α t Y 0)
    {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ (⊤ : ℕ∞) a₀) (p2 n' : ℕ) (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => quietMeanOp Q a₀ p2 n' p.1 X)
      (timeCellMeasure J) := by
  have hsl : ∀ r : ℕ, ContDiff ℝ (r : ℕ∞) a₀ := fun r => ha.of_le (by exact_mod_cast le_top)
  have hbox : ∀ (sX sZ : ℕ), IsBoxSmooth sX sZ (fun X' (_ : Vec 2) => a₀ X') := fun sX sZ =>
    edge_isBoxSmooth_slowOnly (hsl sX)
  have hfi : FastIndep (fun X' (_ : Vec 2) => a₀ X') := fun _ _ _ => rfl
  have hconst : ∀ X', AEStronglyMeasurable (fun p : ℝ × Vec 2 => (fun X'' (_ : Vec 2) => a₀ X'') X'
      p.2) (timeCellMeasure J) := fun X' => aestronglyMeasurable_const
  unfold quietMeanOp
  by_cases h0 : p2 = 0
  · simp only [h0, ↓reduceIte]
    by_cases h2 : n' = 2
    · simp only [h2, ↓reduceIte]
      have := sreg_aesm_cellB2 (η := Q.η) (G := Q.G) (Φ := fun _ X'' (_ : Vec 2) => a₀ X'') hJ hGm
        hGs (fun t _ => hbox 2 0) hconst X
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      exact (FastIndep.cellB2 Q.η Q.G p.1 hfi X 0 p.2).symm
    · simp only [h2, ↓reduceIte]; exact aestronglyMeasurable_const
  · simp only [h0, ↓reduceIte]
    by_cases h1 : p2 = 1
    · simp only [h1, ↓reduceIte]
      have := sreg_aesm_sourceCoeff hJ Q.edge Q.η hquiet hsm hcoef
        (Φ := fun _ X'' (_ : Vec 2) => a₀ X'') (fun t _ => hbox D D)
        (fun t _ X'' n z => rfl) hconst n' X
      refine this.neg.congr ?_
      filter_upwards [ae_timeCell_fst_mem hJ] with p hp
      have := sourceCoeff_fastIndep Q.edge Q.η p.1 n' (hquiet p.1 hp) hfi X 0 p.2
      simp only [Pi.neg_apply, this]
    · simp only [h1, ↓reduceIte]; exact aestronglyMeasurable_const

end Source
end

/-! Joint time-cell measurability of the quiet source `quietSource` of a smooth test field on a
quiet window of the lift. -/

section
open AVRegularity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

variable {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {H N K k L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {b : ι → ι → ℝ} {Θ : ℝ}
    {Cc : ℕ → ℕ → LiftCoeff ι h}

/-- The lift action of the quiet mean operator is a.e. strongly measurable. -/
theorem sreg_aesm_liftApply_quietMean
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    (hseq : IsLiftSequenceFrom Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc)
    {S : Set ℝ} (hSm : MeasurableSet S) (hSc : S.OrdConnected) (hS : S ⊆ Icc t₀ t₁)
    (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ (⊤ : ℕ∞) a₀) {g j : ℕ} (hg : g ≤ H) (hj1 : 1 ≤ j)
    (hjN : j ≤ N) (hjq : j + 1 ≤ qs) (p2 n' : ℕ) (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
      liftApply j (Cc g j) (fun s X' => quietMeanOp Q a₀ p2 n' s X') p.1 X p.2)
      (timeCellMeasure S) := by
  have hv0 : ∀ t ∈ S, ∀ z, Q.v t z = 0 := v_eq_zero_of_quiet hset hq
  have hquiet : ∀ t ∈ S, ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z z',
      γ.coeff α t X z = γ.coeff α t X z' := fun t ht v u d γ hγ α X z z' =>
    hq.2 v u d γ hγ α t ht X z z'
  have hGq : ∀ t ∈ S, ∀ r ≤ qs, ∀ i j, ContDiff ℝ ((r : ℕ) : ℕ∞) (fun X => Q.G t X i j) :=
    fun t ht r hr i j => (hset.G_smooth t (hS ht) i j).of_le (by exact_mod_cast hr)
  have hEq : ∀ t ∈ S, ∀ r ≤ qs, ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
      ContDiff ℝ ((r : ℕ) : ℕ∞) (fun X => γ.coeff α t X z) := fun t ht r hr v u d γ hγ α z =>
    (((hset.coeff_smooth v u d γ hγ α t (hS ht)).isSlowSmooth).1 z).of_le (by exact_mod_cast hr)
  have hqM := sreg_aesm_quietMeanOp (Q := Q) hSm hset.G_meas
    (fun t ht i j => hGq t ht 1 (by omega) i j) hquiet
    (fun t ht v u d γ hγ α z => hEq t ht 1 (by omega) v u d γ hγ α z)
    (fun v u d γ hγ α Y => hset.coeff_meas v u d γ hγ α Y 0) ha
  refine sreg_aesm_pi fun v => ?_
  show AEStronglyMeasurable (fun p : ℝ × Vec 2 => ∑ m ∈ Finset.range (j + 1),
    ∑ α : DerivativeWord2 m, ∑ u : ι, Cc g j m α p.1 X p.2 v u
      (orderedDerivative α (fun X' => quietMeanOp Q a₀ p2 n' p.1 X') X u)) (timeCellMeasure S)
  refine Finset.aestronglyMeasurable_fun_sum _ fun m hm => Finset.aestronglyMeasurable_fun_sum _
    fun α _ => Finset.aestronglyMeasurable_fun_sum _ fun u _ => ?_
  have hmj : m ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  refine sreg_aesm_clm_apply (c := fun p : ℝ × Vec 2 => Cc g j m α p.1 X p.2 v u)
    (w := fun p : ℝ × Vec 2 => orderedDerivative α (fun X' => quietMeanOp Q a₀ p2 n' p.1 X') X u)
    (fun x => sreg_aesm_coeff hseq hg hj1 hjN hmj α v u x
      (fun t ht => hS ht) hSc hv0 X) (fun ℓ' => ?_)
  have hF : ∀ t ∈ S, IsBoxSmooth j 0 (fun X' (_ : Vec 2) => quietMeanOp Q a₀ p2 n' t X') :=
    fun t ht => edge_isBoxSmooth_slowOnly (sreg_quietMeanOp_contDiff Q t hset.D_ge (hquiet t ht) ha
      p2 n' j (fun i i' => hGq t ht (j + 1) hjq i i')
      (fun v' u' d γ hγ α' z => hEq t ht (j + 1) hjq v' u' d γ hγ α' z))
  have h1 := aestronglyMeasurable_orderedDerivative_slow hSm
    (F := fun t X' (_ : Vec 2) => quietMeanOp Q a₀ p2 n' t X') hF (hqM p2 n') α hmj X
  exact ((ℓ'.comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) u)).continuous.comp_aestronglyMeasurable
    h1)

/-- **Measurability of the quiet source** of a smooth test field on a quiet window. -/
theorem sreg_aesm_quietSource
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    (hseq : IsLiftSequenceFrom Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc)
    (hDsZ : D ≤ max (k + 1) (L + 2)) {S : Set ℝ} (hSm : MeasurableSet S) (hSc : S.OrdConnected)
    (hS : S ⊆ Icc t₀ t₁) (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    {hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N) (hnq : n + 1 ≤ qs)
    {a₀ : Vec 2 → ∀ i, h i} (ha : ContDiff ℝ (⊤ : ℕ∞) a₀) (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => quietSource Q Cc a₀ hh n p.1 X p.2)
      (timeCellMeasure S) := by
  have hD2 := hset.D_ge
  have hv0 : ∀ t ∈ S, ∀ z, Q.v t z = 0 := v_eq_zero_of_quiet hset hq
  have hdrift : ∀ t ∈ S, ∀ z, Real.sqrt Q.η • Q.v t z = 0 := fun t ht z => hq.1 t ht z
  have hquiet : ∀ t ∈ S, ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z z',
      γ.coeff α t X z = γ.coeff α t X z' := fun t ht v u d γ hγ α X z z' =>
    hq.2 v u d γ hγ α t ht X z z'
  have hGq : ∀ t ∈ S, ∀ r ≤ qs, ∀ i j, ContDiff ℝ ((r : ℕ) : ℕ∞) (fun X => Q.G t X i j) :=
    fun t ht r hr i j => (hset.G_smooth t (hS ht) i j).of_le (by exact_mod_cast hr)
  have hEq : ∀ t ∈ S, ∀ r ≤ qs, ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
      ContDiff ℝ ((r : ℕ) : ℕ∞) (fun X => γ.coeff α t X z) := fun t ht r hr v u d γ hγ α z =>
    (((hset.coeff_smooth v u d γ hγ α t (hS ht)).isSlowSmooth).1 z).of_le (by exact_mod_cast hr)
  have hao : ∀ r : ℕ, ContDiff ℝ (r : ℕ∞) a₀ := fun r => ha.of_le (by exact_mod_cast le_top)
  have h2Z : 2 ≤ max (k + 1) (L + 2) := le_max_of_le_right (by omega)
  have hmeasLA : ∀ (g M : ℕ), g ≤ H → M ≤ N → ∀ X', AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => liftApply M (Cc g M) (fun _ => a₀) p.1 X' p.2) (timeCellMeasure S) :=
    fun g M hg hM X' => sreg_aesm_liftApply_le hseq hg hM ha hSm hS hSc hv0 X'
  -- the four groups
  have T1 : AEStronglyMeasurable (fun p : ℝ × Vec 2 => if 2 ≤ n then cellB1 Q.η Q.G Q.v p.1
      (liftApply (n - 1) (Cc hh (n - 1)) (fun _ => a₀) p.1) X p.2 else 0) (timeCellMeasure S) := by
    by_cases hn : 2 ≤ n
    · simp only [hn, ↓reduceIte]
      exact sreg_aesm_cellB1 hSm hdrift hset.G_meas (fun t ht i j => hGq t ht 1 (by omega) i j)
        (fun t ht => sreg_liftApply_box hseq hhH (n - 1) (by omega) h2Z _ (hS ht) (hao _))
        (fun t ht X' => sreg_liftApply_per hseq hhH (n - 1) _ (hS ht) X')
        (hmeasLA hh (n - 1) hhH (by omega)) X
    · simp only [hn, ↓reduceIte]; exact aestronglyMeasurable_const
  have T2 : AEStronglyMeasurable (fun p : ℝ × Vec 2 => if 3 ≤ n then cellB2 Q.η Q.G p.1
      (liftApply (n - 2) (Cc hh (n - 2)) (fun _ => a₀) p.1) X p.2 else 0) (timeCellMeasure S) := by
    by_cases hn : 3 ≤ n
    · simp only [hn, ↓reduceIte]
      exact sreg_aesm_cellB2 hSm hset.G_meas (fun t ht i j => hGq t ht 1 (by omega) i j)
        (fun t ht => sreg_liftApply_box hseq hhH (n - 2) (by omega) (Nat.zero_le _) _
          (hS ht) (hao _))
        (hmeasLA hh (n - 2) hhH (by omega)) X
    · simp only [hn, ↓reduceIte]; exact aestronglyMeasurable_const
  have T3 : AEStronglyMeasurable (fun p : ℝ × Vec 2 => if hh = 0 then 0 else
      ∑ j ∈ (Finset.range (min D n + 1)).filter (· < n),
        sourceCoeff Q.edge Q.η j p.1 (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ => a₀) p.1)
          X p.2) (timeCellMeasure S) := by
    by_cases hz : hh = 0
    · simp only [hz, ↓reduceIte]; exact aestronglyMeasurable_const
    · simp only [hz, ↓reduceIte]
      refine Finset.aestronglyMeasurable_fun_sum _ fun j hj => ?_
      have hjn := (Finset.mem_filter.mp hj).2
      exact sreg_aesm_sourceCoeff (Φ := fun t => liftApply (n - j) (Cc (hh - 1) (n - j))
          (fun _ => a₀) t) hSm Q.edge Q.η hquiet
        (fun t ht v u d γ hγ α z => hEq t ht 1 (by omega) v u d γ hγ α z)
        (fun v u d γ hγ α Y => hset.coeff_meas v u d γ hγ α Y 0)
        (fun t ht => sreg_liftApply_box hseq (g := hh - 1) (by omega) (n - j) (by omega) hDsZ _
          (hS ht) (hao _))
        (fun t ht X' => sreg_liftApply_per hseq (g := hh - 1) (by omega) (n - j) _ (hS ht) X')
        (hmeasLA (hh - 1) (n - j) (by omega) (by omega)) j X
  have T4 : AEStronglyMeasurable (fun p : ℝ × Vec 2 => ∑ j ∈ Finset.Icc 1 (n - 2),
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftApply j (Cc q.1 j) (fun s X' => quietMeanOp Q a₀ q.2 (n - j) s X') p.1 X p.2)
      (timeCellMeasure S) := by
    refine Finset.aestronglyMeasurable_fun_sum _ fun j hj => Finset.aestronglyMeasurable_fun_sum _
      fun q hq' => ?_
    have hj' := Finset.mem_Icc.mp hj
    have hq'' := Finset.HasAntidiagonal.mem_antidiagonal.mp hq'
    exact sreg_aesm_liftApply_quietMean hset hseq hSm hSc hS hq ha (by omega) hj'.1 (by omega)
      (by omega) q.2 (n - j) X
  unfold quietSource
  exact (((T1.neg).sub T2).add T3).add T4
end

/-! **Regularity and measurability of the recentred block source** at the quiet times of a window:
`blockSrc` is box smooth of orders `(P + 1, F)` and fast periodic (`sreg_blockSrc_box`), is zero in
the case `hh = 0`, `n = 1` (`sreg_blockSrc_zero`), and is a.e. strongly measurable in time and cell
for the window measure (`sreg_blockSrc_aesm`). All are obtained from the recentring identity with
the fixed centre `X₀ = 0`: a finite combination, with polynomial slow weights, of quiet sources of
fixed polynomial test fields. -/

section
open AVRegularity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

variable {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {H N K k L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {b : ι → ι → ℝ} {Θ : ℝ}
    {Cc : ℕ → ℕ → LiftCoeff ι h}

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
/-- The lift has `N + 1 ≤ qs`. -/
theorem sreg_N_succ_le_qs
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ) :
    N + 1 ≤ qs := by
  have h1 := hset.qs_eq
  have hD := hset.D_ge
  have h2 : N + D ≤ (N + D) ^ 2 := by nlinarith
  have h3 : (N + D) ^ 2 ≤ 4 * (H + 1) * (N + D) ^ 2 := by nlinarith [Nat.zero_le H]
  omega

/-- **Box smoothness and periodicity of the block source at quiet times.** Slow orders `P + 1`,
fast orders `F`; premises `P + 1 + D ≤ K + D + 2`, `F + D ≤ max (k+1) (L+2)`,
`P + N + 2 ≤ qs`. -/
theorem sreg_blockSrc_box
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    (hDsZ : D ≤ max (k + 1) (L + 2))
    (hseq : IsLiftSequenceFrom Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc)
    {S : Set ℝ} (hS : S ⊆ Icc t₀ t₁) (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    {P F : ℕ} (hP : P + 1 + D ≤ K + D + 2) (hF : F + D ≤ max (k + 1) (L + 2))
    (hqs : P + N + 2 ≤ qs) {hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N) {m : ℕ}
    (α : DerivativeWord2 m) (v u : ι) (x : h u) {t : ℝ} (htS : t ∈ S) :
    IsBoxSmooth (P + 1) F (blockSrc Q Cc hh n α v u x t) ∧
      ∀ X, AVenhance.IsZ2Periodic (blockSrc Q Cc hh n α v u x t X) := by
  have hrec : ∀ X' z, blockSrc Q Cc hh n α v u x t X' z =
      ∑ T : Finset (Fin (List.ofFn α).length), cS 0 (List.ofFn α) T X' •
        quietSource Q Cc (subTest u x 0 (List.ofFn α) T) hh n t X' z v := fun X' z =>
    blockSrc_recentre hDsZ hset hseq hS hq hhH hn1 hnN (by omega) α v u x htS 0 X' z
  have hQ := fun T : Finset (Fin (List.ofFn α).length) =>
    sreg_quietSource_box hset hseq hS hq hP hF hqs hhH hn1 hnN
      (contDiff_subTest u x (0 : Vec 2) (List.ofFn α) T) htS
  have e1 : blockSrc Q Cc hh n α v u x t = fun X' z =>
      ∑ T : Finset (Fin (List.ofFn α).length), cS 0 (List.ofFn α) T X' •
        quietSource Q Cc (subTest u x 0 (List.ofFn α) T) hh n t X' z v :=
    funext fun X' => funext fun z => hrec X' z
  rw [e1]
  refine ⟨IsBoxSmooth.sum _ fun T _ => ?_, fun X => sreg_per_sum _ fun T _ => ?_⟩
  · exact ((hQ T).1.map_clm (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)).smul_slow
      (contDiff_cS 0 (List.ofFn α) T _)
  · exact sreg_per_smul _ (fun n' z => congrFun ((hQ T).2 X n' z) v)

/-- At `hh = 0`, `n = 1` the block source vanishes at quiet times. -/
theorem sreg_blockSrc_zero
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    (hDsZ : D ≤ max (k + 1) (L + 2))
    (hseq : IsLiftSequenceFrom Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc)
    {S : Set ℝ} (hS : S ⊆ Icc t₀ t₁) (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    {m : ℕ} (α : DerivativeWord2 m) (v u : ι) (x : h u) {t : ℝ} (htS : t ∈ S) :
    blockSrc Q Cc 0 1 α v u x t = fun _ _ => 0 := by
  funext X' z
  have h1 := quiet_source N K k L D H CG Cw Cj hDsZ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf
    b Θ hset Cc hseq S hS hq (blockTest u x α X') (contDiff_blockTest u x α X') 0 (Nat.zero_le _) 1
    le_rfl hset.N_ge t htS X' z
  simp only [blockSrc]
  rw [h1]
  simp [quietSource]

/-- At `hh = 0`, `n = 1` the block source is box smooth of every order and periodic. -/
theorem sreg_blockSrc_box_zero
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    (hDsZ : D ≤ max (k + 1) (L + 2))
    (hseq : IsLiftSequenceFrom Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc)
    {S : Set ℝ} (hS : S ⊆ Icc t₀ t₁) (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    (P F : ℕ) {m : ℕ} (α : DerivativeWord2 m) (v u : ι) (x : h u) {t : ℝ} (htS : t ∈ S) :
    IsBoxSmooth (P + 1) F (blockSrc Q Cc 0 1 α v u x t) ∧
      ∀ X, AVenhance.IsZ2Periodic (blockSrc Q Cc 0 1 α v u x t X) := by
  rw [sreg_blockSrc_zero hset hDsZ hseq hS hq α v u x htS]
  exact ⟨sreg_boxSmooth_zero _ _, fun X => sreg_per_const 0⟩

/-- **Measurability of the block source** for the window measure, on a quiet window. -/
theorem sreg_blockSrc_aesm
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    (hDsZ : D ≤ max (k + 1) (L + 2))
    (hseq : IsLiftSequenceFrom Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc)
    {S : Set ℝ} (hSm : MeasurableSet S) (hSc : S.OrdConnected) (hS : S ⊆ Icc t₀ t₁)
    (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    {hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N) {m : ℕ}
    (α : DerivativeWord2 m) (v u : ι) (x : h u) (X : Vec 2) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => blockSrc Q Cc hh n α v u x p.1 X p.2)
      (winMeasure S) := by
  have hnq : n + 1 ≤ qs := by have := sreg_N_succ_le_qs hset; omega
  have hsum : AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
      ∑ T : Finset (Fin (List.ofFn α).length), cS 0 (List.ofFn α) T X •
        quietSource Q Cc (subTest u x 0 (List.ofFn α) T) hh n p.1 X p.2 v) (winMeasure S) :=
    Finset.aestronglyMeasurable_fun_sum _ fun T _ =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := h) v).continuous.comp_aestronglyMeasurable
        (sreg_aesm_quietSource hset hseq hDsZ hSm hSc hS hq hhH hn1 hnN hnq
          (contDiff_subTest u x (0 : Vec 2) (List.ofFn α) T) X)).const_smul _
  refine hsum.congr ?_
  filter_upwards [ae_timeCell_fst_mem hSm] with p hp
  exact (blockSrc_recentre hDsZ hset hseq hS hq hhH hn1 hnN hnq α v u x hp 0 X p.2).symm
end

end AVRegularity.QuietDecay
end
