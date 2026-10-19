-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Linear.Main
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
import AVRegularity.CycleComparison.QuietDecay.Scalar.Weighted
public import AVRegularity.CycleComparison.QuietDecay.Test.MonoLift
public import AVRegularity.CycleComparison.QuietDecay.Meas.Words
public import AVRegularity.CycleComparison.QuietDecay.Engine.VectorMixedSharp
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.Sampling.Diagonal
import AVRegularity.CycleComparison.QuietDecay.Jet.Cell
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! The regularity premises `QuietLinearFacts` of the linearity of the quiet source, at a quiet
time of the window, from the premises of the lift, the lift recursion and quietness; and the
vanishing of the drift on a quiet interval. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

section
variable {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {H N K k L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {b : ι → ι → ℝ} {Θ : ℝ}

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- On a quiet interval the drift vanishes (`η > 0`). -/
theorem v_eq_zero_of_quiet
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    {S : Set ℝ} (hq : IsQuietOn Q.edge (fun τ z => Real.sqrt Q.η • Q.v τ z) S) :
    ∀ t ∈ S, ∀ z, Q.v t z = 0 := by
  intro t ht z
  have hη : 0 < Q.η := by rw [hset.η_eq]; exact div_pos hset.ν_pos hset.B_pos
  have h1 := hq.1 t ht z
  exact (smul_eq_zero.1 h1).resolve_left (Real.sqrt_pos.2 hη).ne'

/-- **The linearity premises at a quiet time.** -/
theorem quietLinearFacts_of_setting
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    {Cc : ℕ → ℕ → LiftCoeff ι h} {sX sZ : ℕ} (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc)
    (hDX : D ≤ sX) (hDZ : D ≤ sZ) {S : Set ℝ} (hS : S ⊆ Icc t₀ t₁)
    (hq : IsQuietOn Q.edge (fun τ z => Real.sqrt Q.η • Q.v τ z) S)
    {t : ℝ} (ht : t ∈ S) {hh n : ℕ} (hhH : hh ≤ H) (hn : n + 1 ≤ qs) :
    QuietLinearFacts Q Cc t hh n := by
  have ht' := hS ht
  refine ⟨hset.D_ge, fun p hp j m α v u => ?_, fun i j => ?_, fun v u d γ hγ α X z z' => ?_,
    fun v u d γ hγ α z => ?_⟩
  · obtain ⟨h1, h2⟩ := hseq.2.2.2.2.2.1 p (hp.trans hhH) j m α v u t ht'
    exact ⟨h1.mono hDX hDZ, h2⟩
  · exact (hset.G_smooth t ht' i j).of_le (by exact_mod_cast hn)
  · exact hq.2 v u d γ hγ α t ht X z z'
  · exact (((hset.coeff_smooth v u d γ hγ α t ht').isSlowSmooth).1 z).of_le
      (by exact_mod_cast hn)

end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.QuietDecay

/-! The exact quiet decomposition of the cell source of the lift in a quiet gap, for a lift
sequence from an arbitrary entrance: on quiet times the cell source equals `quietSource`, which
contains no cell mean term and only the explicit means `ℬ₂ I`, `-𝒮_n I` inside the products. -/

open AVRegularity

section Core
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ}

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem liftApply_congr_at (n : ℕ) (c : LiftCoeff ι h) {a a' : ℝ → Vec 2 → ∀ i, h i} {t : ℝ}
    (ha : a t = a' t) : liftApply n c a t = liftApply n c a' t := by
  unfold liftApply
  rw [ha]

theorem QuietFacts.liftMean_eq {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
    {a₀ : Vec 2 → ∀ i, h i} {t : ℝ} {H hh n : ℕ} (hf : QuietFacts Q Cc a₀ t H) (hhH : hh ≤ H)
    (hn : 1 ≤ n) (X : Vec 2) :
    liftMean Q Cc (fun _ => a₀) hh n t X = quietFast Q Cc a₀ hh n t X 0 := by
  have hlead := hf.lead_centField (n := n) hhH
  have hfast := hf.fast_fastIndep (n := n) hhH
  have hc2 : Continuous (quietFast Q Cc a₀ hh n t X) := by
    have : quietFast Q Cc a₀ hh n t X = fun _ => quietFast Q Cc a₀ hh n t X 0 :=
      funext fun z => hfast X z 0
    rw [this]; exact continuous_const
  change fieldCellMean (fun z => liftA Q Cc (fun _ => a₀) hh n t X z) = _
  have e : (fun z => liftA Q Cc (fun _ => a₀) hh n t X z) =
      fun z => quietLead Q Cc a₀ hh n t X z + quietFast Q Cc a₀ hh n t X z :=
    funext fun z => liftA_eq_quietLead_add Q Cc a₀ t (hh := hh) hn X z
  rw [e, fieldCellMean_add (hlead.1.continuous_slice X) hc2, hlead.2 trivial X, zero_add,
    fieldCellMean_fastIndep hfast X]

theorem QuietFacts.liftCellSource_eq {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
    {a₀ : Vec 2 → ∀ i, h i} {t : ℝ} {H hh n : ℕ} (hf : QuietFacts Q Cc a₀ t H) (hhH : hh ≤ H)
    (hn : 1 ≤ n)
    (hmean : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh, ∀ X,
      liftMean Q Cc (fun _ => a₀) p.2 (n - j) t X = quietMeanOp Q a₀ p.2 (n - j) t X)
    (X z : Vec 2) :
    liftCellSource Q Cc (fun _ => a₀) hh n t X z = quietSource Q Cc a₀ hh n t X z := by
  rw [quietSource_eq_neg_lead_add]
  have hfast := hf.fast_fastIndep (n := n) hhH
  have hA := liftA_eq_quietLead_add Q Cc a₀ t (hh := hh) hn X z
  have hm := hf.liftMean_eq hhH hn X
  simp only [liftCellSource]
  rw [hm, hA, ← hfast X z 0]
  have hsum : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftApply j (Cc p.1 j) (liftMean Q Cc (fun _ => a₀) p.2 (n - j)) t X z =
        liftApply j (Cc p.1 j) (fun s X' => quietMeanOp Q a₀ p.2 (n - j) s X') t X z :=
    fun j hj p hp => by
      rw [liftApply_congr_at j (Cc p.1 j) (a' := fun s X' => quietMeanOp Q a₀ p.2 (n - j) s X')
        (funext (hmean j hj p hp))]
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl (hsum j hj)]
  abel

end Core

theorem quiet_source (N K k L D H : ℕ) (CG Cw : ℕ → ℝ)
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
        ∀ n, 1 ≤ n → n ≤ N → ∀ t ∈ S, ∀ X z,
          liftCellSource Q Cc (fun _ => a₀) hh n t X z = quietSource Q Cc a₀ hh n t X z := by
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ hset Cc hseq S hS hq a₀
    ha hh hhH n hn1 hnN t htS X z
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
  have hf : QuietFacts Q Cc a₀ t H :=
    { D_ge := hD2
      G_smooth := fun i j => (hset.G_smooth t htI i j).of_le (by exact_mod_cast hqs1)
      drift := fun z k => by
        have := congrFun (hq.1 t htS z) k
        simpa using this
      edge_quiet := fun v u d γ hγ α X z z' => hq.2 v u d γ hγ α t htS X z z'
      edge_smooth := fun v u d γ hγ α z =>
        ((hset.coeff_smooth v u d γ hγ α t htI).contDiff_slow z).of_le (by exact_mod_cast hqs1)
      good := fun hh' hh'H m =>
        liftApply_goodField_of_seqFrom Q hseq (r := 2) (by omega) (by omega) hh'H m ha htI
      cent := fun hh' hh'H m hm =>
        liftApply_centField_of_seqFrom Q hseq hsX hDsZ hh'H hm ha htI
      fast0 := fun g hg => by
        by_cases hg0 : g = 0
        · subst hg0
          have hbase : liftApply 0 (Cc 0 0) (fun _ => a₀) t = fun X' _ => a₀ X' := by
            funext X' z; exact hseq.1 a₀ ha t htI X' z
          rw [hbase]; exact fun _ _ _ => rfl
        · have h2 : ∀ m α X z v u, Cc g 0 m α t X z v u = 0 := fun m α X z v u =>
            hseq.2.1 g (by omega) hg m α t X z v u
          rw [liftApply_eq_zero _ _ 0 t h2]; exact FastIndep.zero }
  refine hf.liftCellSource_eq hhH hn1 (fun j hj p hp X' => ?_) X z
  have hj := Finset.mem_Icc.mp hj
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  exact quiet_mean_from N K k L D H CG Cw Cj hDsZ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ
    hset Cc hseq S hS hq a₀ ha p.2 (by omega) (n - j) (by omega) (by omega) t htS X'

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.QuietDecay

/-! The engine families of the lift recursion: for a scalar functional `ℓ` and a family of test
fields `X ↦ test X`, the member at the slow point `X` is the cell jet of `ℓ` of the lift action on
the test field `test X`, evaluated at `X`; its source is `ℓ` of the cell source. On a window where the
drift vanishes, these are cell solutions for the slow-point metric. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

/-- The engine family of the level `(hh, n)` for the functional `ℓ` and the test fields `test`. -/
def liftFam (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (ℓ : (∀ i, h i) →L[ℝ] ℝ) (test : Vec 2 → Vec 2 → ∀ i, h i) : CellFam where
  D X := cellJetOfField ℓ (fun t z => liftApply n (Cc hh n) (fun _ => test X) t X z)
  src X t z := ((ℓ (liftCellSource Q Cc (fun _ => test X) hh n t X z) : ℝ) : ℂ)
  F _ _ _ := 0

/-- The metric of the lift operator data at the slow point. -/
def liftMetric (Q : LiftOperatorData ι h D) : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  fun t X => Matrix.of (Q.G t X)

omit [∀ i, CompleteSpace (h i)] in
theorem isCellFam_liftFam {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
    {sX sZ N H : ℕ} {t₀ t₁ : ℝ} (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc)
    {hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N) (ℓ : (∀ i, h i) →L[ℝ] ℝ)
    {test : Vec 2 → Vec 2 → ∀ i, h i} (htest : ∀ X, ContDiff ℝ (⊤ : ℕ∞) (test X))
    {J : Set ℝ} (hJ : J ⊆ Icc t₀ t₁) (hJc : J.OrdConnected) (hv : ∀ t ∈ J, ∀ z, Q.v t z = 0) :
    IsCellFam J (liftMetric Q) (fun _ _ => 0) (liftFam Q Cc hh n ℓ test) := by
  intro X
  have h1 := ((hseq.2.2.2.2.2.2 hh hhH n hn1 hnN (test X) (htest X) X).2 ℓ).1
  have h2 := cellSolution_restrict hJ hJc h1
  exact cellSolution_coeff_congr (C := ⟨fun t _ => Matrix.of (Q.G t X), Q.v, 0, 0⟩)
    (C' := slowCoeffs (liftMetric Q) (fun _ _ => 0) X)
    (fun t _ => rfl) (fun t ht => funext fun z => hv t ht z) rfl (fun t _ => rfl) h2

omit [∀ i, CompleteSpace (h i)] in
theorem liftFam_mean {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
    {sX sZ N H : ℕ} {t₀ t₁ : ℝ} (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc)
    {hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N) (ℓ : (∀ i, h i) →L[ℝ] ℝ)
    {test : Vec 2 → Vec 2 → ∀ i, h i} (htest : ∀ X, ContDiff ℝ (⊤ : ℕ∞) (test X))
    {J : Set ℝ} (hJ : J ⊆ Icc t₀ t₁) (X : Vec 2) (t : ℝ) (ht : t ∈ J) :
    cellMean (cellValue ((liftFam Q Cc hh n ℓ test).D X) t) = 0 :=
  ((hseq.2.2.2.2.2.2 hh hhH n hn1 hnN (test X) (htest X) X).2 ℓ).2.1 t (hJ ht)

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem liftFam_value (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (ℓ : (∀ i, h i) →L[ℝ] ℝ) (test : Vec 2 → Vec 2 → ∀ i, h i) (X : Vec 2) (t : ℝ) (z : Vec 2) :
    cellValue ((liftFam Q Cc hh n ℓ test).D X) t z =
      ((ℓ (liftApply n (Cc hh n) (fun _ => test X) t X z) : ℝ) : ℂ) := by
  simp [liftFam, cellValue, cellJetOfField, valueIndex2, valueIndex]

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! The engine applied to one coefficient block of the lift recursion: the components of the block
`C_{m,α}(·,·,·)(v,u) x` along an orthonormal basis of `h v` form an engine family (test fields
centred at the slow point), so the mixed word derivatives of the block at the time `τ` are bounded by
those at the entrance time and by those of the cell source of the block, with exponential weights. -/

section
variable {κ : Type*} [Fintype κ] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

/-- The centred test field of the word `α` and the vector `x` in the component `u`. -/
def blockTest (u : ι) (x : h u) {m : ℕ} (α : DerivativeWord2 m) (X : Vec 2) : Vec 2 → ∀ i, h i :=
  fun Y => monoF X (List.ofFn α) Y • Pi.single u x

/-- The block `C_{m,α}(t, X, z)(v, u) x`. -/
def blockF (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) {m : ℕ} (α : DerivativeWord2 m) (v u : ι)
    (x : h u) (t : ℝ) : Vec 2 → Vec 2 → h v :=
  fun X z => Cc hh n m α t X z v u x

/-- The `v` component of the cell source of the block family. -/
def blockSrc (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) {m : ℕ}
    (α : DerivativeWord2 m) (v u : ι) (x : h u) (t : ℝ) : Vec 2 → Vec 2 → h v :=
  fun X z => liftCellSource Q Cc (fun _ => blockTest u x α X) hh n t X z v

/-- The coordinate functionals. -/
def coordL (v : ι) (k : Fin (Module.finrank ℝ (h v))) : (∀ i, h i) →L[ℝ] ℝ :=
  (innerSL ℝ ((stdOrthonormalBasis ℝ (h v)) k)) ∘L ContinuousLinearMap.proj v

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem contDiff_blockTest (u : ι) (x : h u) {m : ℕ} (α : DerivativeWord2 m) (X : Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (blockTest u x α X) :=
  (contDiff_monoF X _ _).smul contDiff_const

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem liftApply_blockTest {Cc : ℕ → ℕ → LiftCoeff ι h} {hh n : ℕ}
    (hsym : LiftSymm (Cc hh n)) {m : ℕ} (hm : m ≤ n) (α : DerivativeWord2 m) (v u : ι) (x : h u)
    (t : ℝ) (X z : Vec 2) :
    liftApply n (Cc hh n) (fun _ => blockTest u x α X) t X z v =
      (liftK α : ℝ) • blockF Cc hh n α v u x t X z := by
  have := congrFun (liftApply_monoF hsym n hm α (Pi.single u x) t X z) v
  change liftApply n (Cc hh n) (fun _ Y => monoF X (List.ofFn α) Y • Pi.single u x) t X z v = _
  rw [this]
  simp only [Pi.smul_apply, blockF]
  congr 1
  rw [Finset.sum_eq_single u]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ u) h

section Coord

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The scaled complexified coordinate map. -/
def coordC (b : OrthonormalBasis κ ℝ H) (c : ℝ) (k : κ) : H →L[ℝ] ℂ :=
  Complex.ofRealCLM ∘L (c • innerSL ℝ (b k))

theorem coordC_apply (b : OrthonormalBasis κ ℝ H) (c : ℝ) (k : κ) (w : H) :
    coordC b c k w = ((c * inner ℝ (b k) w : ℝ) : ℂ) := by
  simp [coordC]

theorem slowIter_eq_slowDerivs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : List (Fin 2)) (φ : Vec 2 → Vec 2 → E) : slowIter l φ = slowDerivs l φ := rfl

theorem contDiff_fastDerivsE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} :
    ∀ (m : List (Fin 2)) {g : Vec 2 → E},
      ContDiff ℝ ((k + m.length : ℕ) : ℕ∞) g → ContDiff ℝ (k : ℕ∞) (fastDerivs m g) := by
  intro m
  induction m with
  | nil => intro g hg; simpa [fastDerivs] using hg
  | cons i m ih =>
      intro g hg
      rw [fastDerivs_cons]
      refine ih ?_
      have : ContDiff ℝ (((k + m.length : ℕ) : WithTop ℕ∞) + 1) g := by
        refine hg.of_le ?_
        simp only [List.length_cons]
        exact_mod_cast le_of_eq (by ring)
      exact contDiff_fderiv_apply this i

end Coord

/-- The metric facts of the engine on `[a, b]`. -/
structure MetricData (a b : ℝ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Γ : ℝ) (P : ℕ) :
    Prop where
  Gm : ∀ X i j, Measurable fun t => G t X i j
  Gs : ∀ t ∈ Icc a b, ∀ X i j, G t X i j = G t X j i
  Ge : ∀ t ∈ Icc a b, ∀ X (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t X i j * ξ i * ξ j ∧
    ∑ i, ∑ j, G t X i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2
  Γ0 : 0 ≤ Γ
  Gsmooth : ∀ t ∈ Icc a b, ∀ j k, ContDiff ℝ ((P + 1 : ℕ) : ℕ∞) fun Y => G t Y j k
  Gder : ∀ t ∈ Icc a b, ∀ w : List (Fin 2), w.length ≤ P → ∀ Y j k,
    ‖slowDerivs w (fun X (_ : Vec 2) => G t X j k) Y 0‖ ≤ Γ

/-- The initial mixed data of a field. -/
def mixInit (φ : Vec 2 → Vec 2 → E') (n : ℕ) (m : List (Fin 2)) : ℝ≥0∞ :=
  ⨆ (l : {l : List (Fin 2) // l.length ≤ n}) (X : Vec 2), ∫⁻ z in AVenhance.unitCube,
    ‖fastDerivs m (slowDerivs l.1 φ X) z‖ₑ ^ 2

section Block

variable {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h} {hh n : ℕ} {m : ℕ}
  {α : DerivativeWord2 m} {v u : ι} {x : h u}

omit [∀ i, CompleteSpace (h i)] in
theorem valF_liftFam (hsym : LiftSymm (Cc hh n)) (hm : m ≤ n) (t : ℝ) (k) :
    valF (fun k => liftFam Q Cc hh n (coordL v k) (blockTest u x α)) t k =
      fun X z => coordC (stdOrthonormalBasis ℝ (h v)) (liftK α : ℝ) k (blockF Cc hh n α v u x t X z) := by
  funext X z
  simp only [valF]
  rw [liftFam_value, coordC_apply, coordL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, liftApply_blockTest hsym hm, innerSL_apply_apply, inner_smul_right]

omit [∀ i, CompleteSpace (h i)] in
theorem srcF_liftFam (t : ℝ) (k) :
    srcF (fun k => liftFam Q Cc hh n (coordL v k) (blockTest u x α)) t k =
      fun X z => coordC (stdOrthonormalBasis ℝ (h v)) 1 k (blockSrc Q Cc hh n α v u x t X z) := by
  funext X z
  simp only [srcF, liftFam]
  rw [coordC_apply, coordL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    innerSL_apply_apply, one_mul]
  rfl

end Block
end

/-! The engine for one coefficient block with fast regularity of the order of the fast words only
(`IsBoxSmooth (P + 1) P'` for fast words of length `≤ P'`). -/

section
variable {κ : Type*} [Fintype κ] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

section Coord

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The mixed derivatives of the coordinates of a box-smooth field, summed over the basis. -/
theorem coord_sum_eq_sharp (b : OrthonormalBasis κ ℝ H) (c : ℝ) {P Q' : ℕ}
    {φ : Vec 2 → Vec 2 → H} (hφ : IsBoxSmooth (P + 1) Q' φ) (l : List (Fin 2))
    (hl : l.length ≤ P) (m : List (Fin 2)) (hm : m.length ≤ Q') (X : Vec 2) :
    ∑ k, ∫⁻ z in AVenhance.unitCube,
        ‖fastDerivs m (slowDerivs l (fun X' z' => coordC b c k (φ X' z')) X) z‖ₑ ^ 2 =
      ENNReal.ofReal (c ^ 2) * ∫⁻ z in AVenhance.unitCube,
        ‖fastDerivs m (slowDerivs l φ X) z‖ₑ ^ 2 := by
  have hS : IsSlowSmooth (l.length + 1) φ := hφ.isSlowSmooth.mono (by omega)
  have hB : IsBoxSmooth (P + 1 - l.length + l.length) Q' φ := by
    rwa [Nat.sub_add_cancel (by omega)]
  have hcd : ContDiff ℝ (Q' : ℕ∞) (slowDerivs l φ X) := by
    have := (isBoxSmooth_slowIter l _ φ hB).1 X
    rwa [slowIter_eq_slowDerivs] at this
  have hcdm : ContDiff ℝ (m.length : ℕ∞) (slowDerivs l φ X) :=
    hcd.of_le (by exact_mod_cast hm)
  have e1 : ∀ k, (fun z => fastDerivs m (slowDerivs l (fun X' z' => coordC b c k (φ X' z')) X) z) =
      fun z => coordC b c k (fastDerivs m (slowDerivs l φ X) z) := fun k => by
    rw [slowDerivs_clm (coordC b c k) l hS]
    exact fastDerivs_clm (coordC b c k) m hcdm
  simp_rw [e1, coordC_apply]
  have hcont : Continuous (fastDerivs m (slowDerivs l φ X)) :=
    (contDiff_fastDerivsE (k := 0) m (hcd.of_le (by exact_mod_cast (by omega :
      0 + m.length ≤ Q')))).continuous
  have hm : ∀ k, AEMeasurable (fun z =>
      ‖((c * inner ℝ (b k) (fastDerivs m (slowDerivs l φ X) z) : ℝ) : ℂ)‖ₑ ^ 2)
      (volume.restrict AVenhance.unitCube) := fun k =>
    ((((Complex.continuous_ofReal.comp (continuous_const.mul
      ((innerSL ℝ (b k)).continuous.comp hcont))).enorm).measurable.pow_const 2)).aemeasurable
  rw [← lintegral_finsetSum' _ fun k _ => hm k]
  simp_rw [sum_enorm_sq_coord]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end Coord

section Block

variable {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h} {hh n : ℕ} {m : ℕ}
  {α : DerivativeWord2 m} {v u : ι} {x : h u}

omit [∀ i, CompleteSpace (h i)] in
/-- **The engine for one coefficient block.** The mixed word derivatives of the block at the time
`τ` are bounded by those at the entrance time `a` and those of the block source, with exponential
weights. -/
theorem block_engine_sharp {sX sZ N H : ℕ} {t₀ t₁ : ℝ} (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc)
    (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N) (hsym : LiftSymm (Cc hh n)) (hm : m ≤ n)
    {a b : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ Icc t₀ t₁) (hv0 : ∀ t ∈ Icc a b, ∀ z, Q.v t z = 0)
    {Γ : ℝ} {P P' : ℕ} (hG : MetricData a b (liftMetric Q) Γ P)
    (hB : ∀ t ∈ Icc a b, IsBoxSmooth (P + 1) P' (blockF Cc hh n α v u x t) ∧
      ∀ X, AVenhance.IsZ2Periodic (blockF Cc hh n α v u x t X))
    (hS : ∀ t ∈ Icc a b, IsBoxSmooth (P + 1) P' (blockSrc Q Cc hh n α v u x t) ∧
      ∀ X, AVenhance.IsZ2Periodic (blockSrc Q Cc hh n α v u x t X))
    (hSm : ∀ X, AEStronglyMeasurable (fun p : ℝ × Vec 2 => blockSrc Q Cc hh n α v u x p.1 X p.2)
      (winMeasure (Icc a b)))
    (l : List (Fin 2)) (hl : l.length ≤ P) (m' : List (Fin 2)) (hm' : m'.length ≤ P')
    (X : Vec 2) {τ : ℝ} (hτ : τ ∈ Icc a b) :
    ∫⁻ z in AVenhance.unitCube, ‖fastDerivs m' (slowDerivs l (blockF Cc hh n α v u x τ) X) z‖ₑ ^ 2 ≤
      engK Γ l.length * (wt τ a * mixInit (blockF Cc hh n α v u x a) l.length m' +
        ∫⁻ σ in Icc a τ, wt τ σ * mixInit (blockSrc Q Cc hh n α v u x σ) l.length m') := by
  set bv := stdOrthonormalBasis ℝ (h v)
  set Φ : Fin (Module.finrank ℝ (h v)) → CellFam := fun k =>
    liftFam Q Cc hh n (coordL v k) (blockTest u x α)
  set K : ℝ := (liftK α : ℝ)
  have hK1 : (1 : ℝ) ≤ K := Nat.one_le_cast.2 (one_le_liftK α)
  have hvalΦ := fun t k => valF_liftFam (Q := Q) (v := v) (x := x) (α := α) hsym hm t k
  have hsrcΦ := fun t k => srcF_liftFam (Q := Q) (Cc := Cc) (hh := hh) (n := n) (α := α) (v := v)
    (x := x) t k
  have hfam : ∀ k, IsCellFam (Icc a b) (liftMetric Q) (fun _ _ => 0) (Φ k) := fun k =>
    isCellFam_liftFam hseq hhH hn1 hnN (coordL v k) (contDiff_blockTest u x α) hJ ordConnected_Icc
      hv0
  have hED : ∀ k, EngineData a b (liftMetric Q) (Φ k) Γ P := fun k => by
    refine ⟨hab, hG.Gm, hG.Gs, hG.Ge, hfam k, rfl,
      fun X t ht => liftFam_mean hseq hhH hn1 hnN (coordL v k) (contDiff_blockTest u x α) hJ X t ht,
      fun X => ?_, hG.Γ0, hG.Gsmooth, hG.Gder, fun t ht => ?_, fun t ht => ?_⟩
    · have := (coordC bv 1 k).continuous.comp_aestronglyMeasurable (hSm X)
      have e : Function.uncurry ((Φ k).src X) =
          fun p : ℝ × Vec 2 => coordC bv 1 k (blockSrc Q Cc hh n α v u x p.1 X p.2) := by
        funext p; exact congrFun (congrFun (hsrcΦ p.1 k) X) p.2
      rw [e]; exact this
    · have e : (fun X z => cellValue ((Φ k).D X) t z) =
          fun X z => coordC bv K k (blockF Cc hh n α v u x t X z) := hvalΦ t k
      rw [e]
      exact (hB t ht).1.isSlowSmooth.clm_comp (coordC bv K k)
    · have e : (fun X z => (Φ k).src X t z) =
          fun X z => coordC bv 1 k (blockSrc Q Cc hh n α v u x t X z) := hsrcΦ t k
      rw [e]
      exact (hS t ht).1.isSlowSmooth.clm_comp (coordC bv 1 k)
  have hsrcP : ∀ k X, ∀ t ∈ Icc a b, AVenhance.IsZ2Periodic ((Φ k).src X t) := by
    intro k X t ht nn z
    have e : (Φ k).src X t = fun z => coordC bv 1 k (blockSrc Q Cc hh n α v u x t X z) :=
      congrFun (hsrcΦ t k) X
    rw [e]
    simp only [(hS t ht).2 X nn z]
  have hreg : ∀ (φ : Vec 2 → Vec 2 → h v) (c : ℝ) (k : Fin (Module.finrank ℝ (h v))),
      IsBoxSmooth (P + 1) P' φ → (∀ X, AVenhance.IsZ2Periodic (φ X)) →
      ∀ l : List (Fin 2), l.length ≤ P → ∀ X,
        ContDiff ℝ (P' : ℕ∞) (slowDerivs l (fun X' z' => coordC bv c k (φ X' z')) X) ∧
        AVenhance.IsZ2Periodic (slowDerivs l (fun X' z' => coordC bv c k (φ X' z')) X) := by
    intro φ c k hφ hper l hl X
    rw [slowDerivs_clm (coordC bv c k) l (hφ.isSlowSmooth.mono (by omega))]
    have hB' : IsBoxSmooth (P + 1 - l.length + l.length) P' φ := by
      rwa [Nat.sub_add_cancel (by omega)]
    have h1 := (isBoxSmooth_slowIter l _ φ hB').1 X
    have h2 := periodic_slowIter l φ hper X
    rw [slowIter_eq_slowDerivs] at h1 h2
    refine ⟨(coordC bv c k).contDiff.comp h1, fun nn z => ?_⟩
    simp only [h2 nn z]
  have hvalF : ∀ k, ∀ t ∈ Icc a b, ∀ l : List (Fin 2), l.length ≤ P → ∀ X,
      ContDiff ℝ (P' : ℕ∞) (slowDerivs l (valF Φ t k) X) ∧
      AVenhance.IsZ2Periodic (slowDerivs l (valF Φ t k) X) := by
    intro k t ht l hl X
    rw [hvalΦ t k]
    exact hreg _ K k (hB t ht).1 (hB t ht).2 l hl X
  have hsrcF : ∀ k, ∀ t ∈ Icc a b, ∀ l : List (Fin 2), l.length ≤ P → ∀ X,
      ContDiff ℝ (P' : ℕ∞) (slowDerivs l (srcF Φ t k) X) ∧
      AVenhance.IsZ2Periodic (slowDerivs l (srcF Φ t k) X) := by
    intro k t ht l hl X
    rw [hsrcΦ t k]
    exact hreg _ 1 k (hS t ht).1 (hS t ht).2 l hl X
  have hE := engine_mixedV_sharp hab hED hsrcP P' hvalF hsrcF l hl m' hm' X hτ
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hL : ∑ k, ∫⁻ z in AVenhance.unitCube, ‖fastDerivs m' (slowDerivs l (valF Φ τ k) X) z‖ₑ ^ 2 =
      ENNReal.ofReal (K ^ 2) * ∫⁻ z in AVenhance.unitCube,
        ‖fastDerivs m' (slowDerivs l (blockF Cc hh n α v u x τ) X) z‖ₑ ^ 2 := by
    rw [Finset.sum_congr rfl fun k _ => by rw [show valF Φ τ k = _ from hvalΦ τ k]]
    exact coord_sum_eq_sharp bv K (hB τ hτ).1 l hl m' hm' X
  have hI : initMDV a Φ l.length m' ≤
      ENNReal.ofReal (K ^ 2) * mixInit (blockF Cc hh n α v u x a) l.length m' := by
    refine iSup_le fun l' => iSup_le fun X' => ?_
    rw [Finset.sum_congr rfl fun k _ => by rw [show valF Φ a k = _ from hvalΦ a k]]
    rw [coord_sum_eq_sharp bv K (hB a ha).1 l'.1 (l'.2.trans hl) m' hm' X']
    exact mul_le_mul_of_nonneg_left (le_iSup_of_le l' (le_iSup (fun X'' => ∫⁻ z in AVenhance.unitCube,
      ‖fastDerivs m' (slowDerivs l'.1 (blockF Cc hh n α v u x a) X'') z‖ₑ ^ 2) X')) zero_le
  have hSr : ∀ σ ∈ Icc a b, srcMDV Φ l.length m' σ ≤
      mixInit (blockSrc Q Cc hh n α v u x σ) l.length m' := by
    intro σ hσ
    refine iSup_le fun l' => iSup_le fun X' => ?_
    rw [Finset.sum_congr rfl fun k _ => by rw [show srcF Φ σ k = _ from hsrcΦ σ k]]
    rw [coord_sum_eq_sharp bv 1 (hS σ hσ).1 l'.1 (l'.2.trans hl) m' hm' X']
    simp only [one_pow, ENNReal.ofReal_one, one_mul]
    exact le_iSup_of_le l' (le_iSup (fun X'' => ∫⁻ z in AVenhance.unitCube,
      ‖fastDerivs m' (slowDerivs l'.1 (blockSrc Q Cc hh n α v u x σ) X'') z‖ₑ ^ 2) X')
  have hK2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (K ^ 2) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have hK0 : ENNReal.ofReal (K ^ 2) ≠ 0 := (zero_lt_one.trans_le hK2).ne'
  rw [hL] at hE
  refine (ENNReal.mul_le_mul_iff_right hK0 ENNReal.ofReal_ne_top).1 (hE.trans ?_)
  calc engK Γ l.length * (wt τ a * initMDV a Φ l.length m' +
        ∫⁻ σ in Icc a τ, wt τ σ * srcMDV Φ l.length m' σ)
      ≤ engK Γ l.length * (wt τ a * (ENNReal.ofReal (K ^ 2) *
          mixInit (blockF Cc hh n α v u x a) l.length m') + ENNReal.ofReal (K ^ 2) *
          ∫⁻ σ in Icc a τ, wt τ σ * mixInit (blockSrc Q Cc hh n α v u x σ) l.length m') := by
        refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hI zero_le) ?_) zero_le
        refine le_trans ?_ (le_mul_of_one_le_left zero_le hK2)
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
        exact mul_le_mul_of_nonneg_left (hSr σ ⟨hσ.1, hσ.2.trans hτ.2⟩) zero_le
    _ = _ := by ring

end Block
end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! The engine words and the target jets: a fast word of a slow word of a box-smooth field is the
slow word of the fast word (Schwarz), so the vector jet of an operator field applied to a unit
vector is at most the mixed cell jet of the operator norms. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slowDerivs_eq_slowL : ∀ (l : List (Fin 2)) (F : Vec 2 → Vec 2 → E),
    slowDerivs l F = FastJets.slowL l F := by
  intro l
  induction l with
  | nil => intro F; rfl
  | cons i l ih =>
      intro F
      rw [slowDerivs_cons, FastJets.slowL_cons, ih]

theorem fastDerivs_eq_odL (m : List (Fin 2)) (g : Vec 2 → E) :
    fastDerivs m g = FastJets.odL m g := rfl

/-- Schwarz in list form. -/
theorem fastDerivs_slowDerivs_eq_odL {F : Vec 2 → Vec 2 → E} (l m : List (Fin 2))
    (hF : IsBoxSmooth l.length m.length F) (X z : Vec 2) :
    fastDerivs m (slowDerivs l F X) z = FastJets.odL l (fun X' => FastJets.odL m (F X') z) X := by
  have h := congrFun (congrFun (MixedTail.fastL_slowL_comm l m hF) X) z
  simp only [FastJets.fastL, FastJets.slowL] at h
  rw [fastDerivs_eq_odL, slowDerivs_eq_slowL]
  exact h

/-- **Schwarz**: the engine word (fast of slow) is the target word (slow of fast). -/
theorem fastDerivs_slowDerivs_eq {F : Vec 2 → Vec 2 → E} (l m : List (Fin 2))
    (hF : IsBoxSmooth l.length m.length F) (X z : Vec 2) :
    fastDerivs m (slowDerivs l F X) z =
      orderedDerivative (m := l.length) l.get
        (fun X' => orderedDerivative (m := m.length) m.get (F X') z) X := by
  have h := congrFun (congrFun (MixedTail.fastL_slowL_comm l m hF) X) z
  simp only [FastJets.fastL, FastJets.slowL] at h
  rw [fastDerivs_eq_odL, slowDerivs_eq_slowL]
  rw [FastJets.orderedDerivative_eq_odL, List.ofFn_get]
  have e : (fun X' => orderedDerivative (m := m.length) m.get (F X') z) =
      fun X' => FastJets.odL m (F X') z := by
    funext X'; rw [FastJets.orderedDerivative_eq_odL, List.ofFn_get]
  rw [e]
  exact h

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- The engine word of an operator field applied to a fixed vector is the target word applied to
the vector. -/
theorem fastDerivs_slowDerivs_apply {f : Vec 2 → Vec 2 → (E →L[ℝ] F')} {sX sZ : ℕ}
    (hf : IsBoxSmooth sX sZ f) (l m : List (Fin 2)) (hl : l.length + 1 ≤ sX) (hm : m.length ≤ sZ)
    (X z : Vec 2) (η : E) :
    fastDerivs m (slowDerivs l (fun X z => f X z η) X) z =
      FastJets.odL l (fun X' => FastJets.odL m (f X') z) X η := by
  set L : (E →L[ℝ] F') →L[ℝ] F' := ContinuousLinearMap.apply ℝ F' η
  have hS : IsSlowSmooth (l.length + 1) f := hf.isSlowSmooth.mono hl
  have hB : IsBoxSmooth (sX - l.length + l.length) sZ f := by
    rwa [Nat.sub_add_cancel (by omega)]
  have hcd : ContDiff ℝ (m.length : ℕ∞) (slowDerivs l f X) := by
    have := (isBoxSmooth_slowIter l _ _ hB).1 X
    exact (by rwa [slowIter_eq_slowDerivs] at this : ContDiff ℝ (sZ : ℕ∞) _).of_le
      (by exact_mod_cast hm)
  have e1 : fastDerivs m (slowDerivs l (fun X z => f X z η) X) =
      fun z => L (fastDerivs m (slowDerivs l f X) z) := by
    have := slowDerivs_clm L l hS
    simp only [L, ContinuousLinearMap.apply_apply] at this ⊢
    rw [this]
    exact fastDerivs_clm L m hcd
  rw [e1]
  simp only [L, ContinuousLinearMap.apply_apply]
  rw [fastDerivs_slowDerivs_eq_odL l m (hf.mono (by omega) hm) X z]

/-- The vector jet of an operator field applied to a unit vector is at most the mixed cell jet. -/
theorem vecJ_apply_le_mixedCellL2Jet {f : ℝ → Vec 2 → Vec 2 → (E →L[ℝ] F')} {I : Set ℝ} {τ : ℝ}
    (hτ : τ ∈ I) {sX sZ : ℕ} (hf : IsBoxSmooth sX sZ (f τ)) (l m : List (Fin 2))
    (hl : l.length + 1 ≤ sX) (hm : m.length ≤ sZ) (X : Vec 2) (η : E) (hη : ‖η‖ ≤ 1) :
    vecJ (fun X z => f τ X z η) X l m ≤ mixedCellL2Jet I l.length m.length f := by
  set L : (E →L[ℝ] F') →L[ℝ] F' := ContinuousLinearMap.apply ℝ F' η
  have hS : IsSlowSmooth (l.length + 1) (f τ) := hf.isSlowSmooth.mono hl
  have hB : IsBoxSmooth (sX - l.length + l.length) sZ (f τ) := by
    rwa [Nat.sub_add_cancel (by omega)]
  have hcd : ContDiff ℝ (m.length : ℕ∞) (slowDerivs l (f τ) X) := by
    have := (isBoxSmooth_slowIter l _ _ hB).1 X
    exact (by rwa [slowIter_eq_slowDerivs] at this : ContDiff ℝ (sZ : ℕ∞) _).of_le
      (by exact_mod_cast hm)
  have e1 : (fun z => fastDerivs m (slowDerivs l (fun X z => f τ X z η) X) z) =
      fun z => L (fastDerivs m (slowDerivs l (f τ) X) z) := by
    have := slowDerivs_clm L l hS
    simp only [L, ContinuousLinearMap.apply_apply] at this ⊢
    rw [this]
    exact fastDerivs_clm L m hcd
  unfold vecJ
  rw [e1]
  have hB' : IsBoxSmooth l.length m.length (f τ) := hf.mono (by omega) hm
  have e2 : ∀ z, fastDerivs m (slowDerivs l (f τ) X) z =
      orderedDerivative (m := l.length) l.get
        (fun X' => orderedDerivative (m := m.length) m.get (f τ X') z) X :=
    fun z => fastDerivs_slowDerivs_eq l m hB' X z
  calc eLpNorm (fun z => L (fastDerivs m (slowDerivs l (f τ) X) z)) 2
        (volume.restrict AVenhance.unitCube)
      ≤ eLpNorm (fun z => orderedDerivative (m := l.length) l.get
          (fun X' => orderedDerivative (m := m.length) m.get (f τ X') z) X) 2
          (volume.restrict AVenhance.unitCube) := by
        have hc0 : ContDiff ℝ ((0 + m.length : ℕ) : ℕ∞) (slowDerivs l (f τ) X) := by
          simpa using hcd
        refine eLpNorm_mono (L.continuous.comp
          (contDiff_fastDerivsE (k := 0) m hc0).continuous).aestronglyMeasurable fun z => ?_
        rw [e2 z]
        simp only [L, ContinuousLinearMap.apply_apply]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (le_trans (mul_le_mul_of_nonneg_left hη (norm_nonneg _)) (by rw [mul_one]))
    _ ≤ mixedCellL2Jet I l.length m.length f := by
        unfold mixedCellL2Jet
        exact le_iSup₂_of_le τ hτ (le_iSup_of_le X (le_iSup_of_le l.get (le_iSup_of_le m.get le_rfl)))
end

/-! The metric data of the engine from the premises `IsLiftSetting`: on a subwindow, the metric is
measurable in time, symmetric, uniformly elliptic, `C^{P+1}` in the slow variable, and its slow
word derivatives through the order `P ≤ q_s - 1` are bounded by `Γ_P = Σ_{r ≤ P} max (C_G r) 0`
(the slow scale `λ ≤ 1` is dropped). -/

section
/-- Slow word derivatives of a slow-only field, as ordered derivatives (any target space). -/
theorem slowDerivs_eq_orderedDerivative_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : List (Fin 2)) (φ : Vec 2 → Vec 2 → E) (X z : Vec 2) :
    slowDerivs l φ X z = orderedDerivative (m := l.length) l.get (fun X' => φ X' z) X := by
  unfold orderedDerivative
  rw [List.ofFn_get]
  induction l generalizing φ with
  | nil => rfl
  | cons i l ih =>
      rw [slowDerivs_cons, ih]
      rfl

theorem norm_iteratedFDeriv_pi_proj_le {κ : Type*} [Fintype κ] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : Vec 2 → κ → F} {i : ℕ} {X : Vec 2} (hg : ContDiff ℝ (i : ℕ∞) g)
    (k : κ) : ‖iteratedFDeriv ℝ i (fun Y => g Y k) X‖ ≤ ‖iteratedFDeriv ℝ i g X‖ := by
  have hP : ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => F) k)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
      rw [one_mul]; exact norm_le_pi_norm g k
  have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => F) k).norm_iteratedFDeriv_comp_left
    (hg.contDiffAt (x := X)) (n := i) (by exact_mod_cast le_rfl)
  refine this.trans ?_
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ i g X‖ := by gcongr
    _ = _ := one_mul _

/-- The metric bound of the order `P`. -/
def metricΓ (CG : ℕ → ℝ) (P : ℕ) : ℝ := ∑ r ∈ Finset.range (P + 1), max (CG r) 0

theorem metricΓ_nonneg (CG : ℕ → ℝ) (P : ℕ) : 0 ≤ metricΓ CG P :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem le_metricΓ (CG : ℕ → ℝ) {P r : ℕ} (hr : r ≤ P) : max (CG r) 0 ≤ metricΓ CG P :=
  Finset.single_le_sum (f := fun r => max (CG r) 0) (fun _ _ => le_max_right _ _)
    (Finset.mem_range.2 (by omega))

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}

/-- **The metric data from the premises of the lift.** -/
theorem metricData_of_setting {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {H N K k L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {b : ι → ι → ℝ} {Θ : ℝ}
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    {a a' : ℝ} (hJ : Icc a a' ⊆ Icc t₀ t₁) {P : ℕ} (hP : P + 1 ≤ qs) :
    MetricData a a' (liftMetric Q) (metricΓ CG P) P := by
  have hlam0 : 0 ≤ lam := by rw [hset.lam_eq]; exact div_nonneg hset.ρ_pos.le hset.E_pos.le
  refine ⟨fun X i j => hset.G_meas X i j, fun t _ X i j => hset.G_symm t X i j,
    fun t ht X ξ => hset.G_ellip t (hJ ht) X ξ, metricΓ_nonneg CG P,
    fun t ht j k => (hset.G_smooth t (hJ ht) j k).of_le (by exact_mod_cast hP), ?_⟩
  intro t ht w hw Y j k
  have ht' := hJ ht
  -- the whole metric is `C^{qs}` in the slow variable
  have hGs : ContDiff ℝ (qs : ℕ∞) (fun X' => Q.G t X') :=
    contDiff_pi.2 fun j => contDiff_pi.2 fun k => hset.G_smooth t ht' j k
  have hGw : ContDiff ℝ (w.length : ℕ∞) (fun X' => Q.G t X') := hGs.of_le (by exact_mod_cast (by omega))
  have hGj : ContDiff ℝ (w.length : ℕ∞) (fun X' => Q.G t X' j) := contDiff_pi.1 hGw j
  have hGjk : ContDiff ℝ (w.length : ℕ∞) (fun X' => Q.G t X' j k) := contDiff_pi.1 hGj k
  show ‖slowDerivs w (fun X (_ : Vec 2) => liftMetric Q t X j k) Y 0‖ ≤ metricΓ CG P
  simp only [liftMetric, Matrix.of_apply]
  rw [slowDerivs_eq_orderedDerivative_gen,
    Sampling.orderedDerivative_eq_iteratedFDeriv (m := w.length) w.get _ hGjk]
  refine ((iteratedFDeriv ℝ w.length (fun X' => Q.G t X' j k) Y).le_opNorm _).trans ?_
  simp only [norm_basisVec, Finset.prod_const_one, mul_one]
  refine (norm_iteratedFDeriv_pi_proj_le hGj k).trans ((norm_iteratedFDeriv_pi_proj_le hGw j).trans ?_)
  -- the jet bound of the premises
  have hJ1 := hset.G_jets w.length (by omega)
  have hle : ‖iteratedFDeriv ℝ w.length (fun X' => Q.G t X') Y‖ₑ ≤
      ENNReal.ofReal (CG w.length * lam ^ w.length) :=
    le_trans (le_trans (le_iSup (fun Y' => ‖iteratedFDeriv ℝ w.length (fun X' => Q.G t X') Y'‖ₑ) Y)
      (le_iSup₂ (f := fun t' _ => ⨆ Y' : Vec 2,
        ‖iteratedFDeriv ℝ w.length (fun X' => Q.G t' X') Y'‖ₑ) t ht')) hJ1
  have hreal : ‖iteratedFDeriv ℝ w.length (fun X' => Q.G t X') Y‖ ≤
      max (CG w.length * lam ^ w.length) 0 := by
    rw [← ofReal_norm] at hle
    have := (ENNReal.ofReal_le_ofReal_iff' ).1 hle
    rcases this with h1 | h1
    · exact h1.trans (le_max_left _ _)
    · exact h1.trans (le_max_right _ _)
  refine hreal.trans (le_trans ?_ (le_metricΓ CG (r := w.length) (by omega)))
  have hlp : lam ^ w.length ≤ 1 := pow_le_one₀ hlam0 hset.lam_le
  have hl0 : 0 ≤ lam ^ w.length := pow_nonneg hlam0 _
  rcases le_total 0 (CG w.length) with hc | hc
  · refine max_le_max ?_ le_rfl
    calc CG w.length * lam ^ w.length ≤ CG w.length * 1 := by gcongr
      _ = CG w.length := mul_one _
  · exact max_le (le_trans (mul_nonpos_of_nonpos_of_nonneg hc hl0) (le_max_right _ _))
      (le_max_right _ _)
end

/-! The operator norms at the end of the recursion: the mixed cell jet of an operator field at one
time is at most `28` times a bound of the vector jets (unit input vectors, slow words of length
`p`, fast words of length `≤ q + 2`), by the periodic Sobolev bound in the fast variable. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

theorem volume_unitCube_eq_one : volume (AVenhance.unitCube : Set (Vec 2)) = 1 := by
  rw [AVenhance.unitCube, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

theorem fastIter_eq_fastDerivs {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] :
    ∀ (l : List (Fin 2)) (Φ : Vec 2 → Vec 2 → G) (X : Vec 2), fastIter l Φ X = fastDerivs l (Φ X) := by
  intro l
  induction l with
  | nil => intro Φ X; rfl
  | cons i l ih =>
      intro Φ X
      show fastIter l (fastPartial i Φ) X = _
      rw [ih]
      rfl

theorem fastDerivs_append {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (m m' : List (Fin 2)) (g : Vec 2 → G) :
    fastDerivs (m ++ m') g = fastDerivs m' (fastDerivs m g) := by
  simp [fastDerivs, List.foldl_append]

/-- The sum of the Sobolev bound over words of length `< 3`. -/
theorem sum_words_three_le (B : ℝ≥0∞) :
    ∑ k ∈ Finset.range 3, ∑ _β : DerivativeWord2 k, B = 7 * B := by
  simp only [Finset.sum_const, Finset.card_univ, DerivativeWord2, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  norm_num
  ring

/-- **Operator norms by the Sobolev bound.** -/
theorem mixedCellL2Jet_singleton_le {f : ℝ → Vec 2 → Vec 2 → (E →L[ℝ] F')} {τ : ℝ} {sX sZ : ℕ}
    (hf : IsBoxSmooth sX sZ (f τ)) (hper : ∀ X, AVenhance.IsZ2Periodic (f τ X)) {p q : ℕ}
    (hp : p + 1 ≤ sX) (hq : q + 2 ≤ sZ) {B : ℝ≥0∞}
    (hB : ∀ (X : Vec 2) (l mm : List (Fin 2)), l.length = p → mm.length ≤ q + 2 → ∀ η : E,
      ‖η‖ ≤ 1 → vecJ (fun X z => f τ X z η) X l mm ≤ B) :
    mixedCellL2Jet {τ} p q f ≤ 28 * B := by
  unfold mixedCellL2Jet
  refine iSup₂_le fun t ht => ?_
  rw [mem_singleton_iff] at ht
  subst ht
  refine iSup_le fun X => iSup_le fun α => iSup_le fun β => ?_
  set W : Vec 2 → (E →L[ℝ] F') := fun z => orderedDerivative α
    (fun X' => orderedDerivative β (f t X') z) X with hW
  have hWc : Continuous W :=
    continuous_orderedDerivative_orderedDerivative hf (by omega) (by omega) α β X
  -- the pointwise bound on the vectors
  have hvec : ∀ z (η : E), ‖η‖ ≤ 1 → ‖W z η‖ₑ ≤ 28 * B := by
    intro z η hη
    set l := List.ofFn α
    set mm := List.ofFn β
    have hl : l.length = p := List.length_ofFn
    have hmm : mm.length = q := List.length_ofFn
    set g : Vec 2 → F' := fastDerivs mm (slowDerivs l (fun X z => f t X z η) X) with hg
    have hgW : ∀ z, g z = W z η := fun z => by
      rw [hg, fastDerivs_slowDerivs_apply hf l mm (by omega) (by omega) X z η]
      rfl
    have hfη : IsBoxSmooth sX sZ (fun X z => f t X z η) :=
      hf.clm_comp (ContinuousLinearMap.apply ℝ F' η)
    have hBs : IsBoxSmooth (sX - l.length + l.length) sZ (fun X z => f t X z η) := by
      rwa [Nat.sub_add_cancel (by omega)]
    have hcd : ContDiff ℝ (sZ : ℕ∞) (slowDerivs l (fun X z => f t X z η) X) := by
      have := (isBoxSmooth_slowIter l _ _ hBs).1 X
      rwa [slowIter_eq_slowDerivs] at this
    have hg2 : ContDiff ℝ 2 g := by
      have : ContDiff ℝ ((2 + mm.length : ℕ) : ℕ∞) (slowDerivs l (fun X z => f t X z η) X) :=
        hcd.of_le (by exact_mod_cast (by omega))
      exact_mod_cast contDiff_fastDerivsE (k := 2) mm this
    have hgp : AVenhance.IsZ2Periodic g := by
      have hpη : ∀ X', AVenhance.IsZ2Periodic (fun z => f t X' z η) := fun X' nn z => by
        simp only [hper X' nn z]
      have h1 := periodic_slowIter l _ hpη X
      have h2 := periodic_fastIter mm (slowIter l (fun X z => f t X z η)) (periodic_slowIter l _ hpη) X
      rw [fastIter_eq_fastDerivs, slowIter_eq_slowDerivs] at h2
      exact h2
    have hS := periodic_sup_le_sobolev hg2 hgp z
    rw [← hgW z]
    refine hS.trans ?_
    rw [mul_comm 28 B, show (28 : ℝ≥0∞) = 4 * 7 by norm_num, mul_comm B, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [← sum_words_three_le B, mul_comm] at *
    refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun γ _ => ?_
    have hk3 : k ≤ 2 := by have := Finset.mem_range.1 hk; omega
    have e : orderedDerivative γ g = fastDerivs (mm ++ List.ofFn γ) (slowDerivs l (fun X z => f t X z η) X) := by
      rw [fastDerivs_append, FastJets.orderedDerivative_eq_odL]
      rfl
    rw [e]
    have hv := hB X l (mm ++ List.ofFn γ) hl (by simp [hmm]; omega) η hη
    unfold vecJ at hv
    have hc : Continuous (fastDerivs (mm ++ List.ofFn γ) (slowDerivs l (fun X z => f t X z η) X)) := by
      have : ContDiff ℝ ((0 + (mm ++ List.ofFn γ).length : ℕ) : ℕ∞)
          (slowDerivs l (fun X z => f t X z η) X) :=
        hcd.of_le (by exact_mod_cast (by simp [hmm]; omega))
      exact (contDiff_fastDerivsE (k := 0) _ this).continuous
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hc.aestronglyMeasurable] at hv
    simpa [ENNReal.toReal_ofNat] using hv
  -- operator norms
  rcases eq_or_ne B ⊤ with hBt | hBt
  · simp [hBt]
  have hfin : 28 * B ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hBt
  have hop : ∀ z, ‖W z‖ₑ ≤ 28 * B := by
    intro z
    have hM : ∀ η : E, ‖W z η‖ ≤ (28 * B).toReal * ‖η‖ := by
      intro η
      rcases eq_or_ne η 0 with h0 | h0
      · simp [h0]
      have hn : 0 < ‖η‖ := norm_pos_iff.2 h0
      have hu : ‖‖η‖⁻¹ • η‖ ≤ 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      have h1 := hvec z (‖η‖⁻¹ • η) hu
      have h2 : ‖W z (‖η‖⁻¹ • η)‖ ≤ (28 * B).toReal := by
        rw [← ofReal_norm] at h1
        exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 h1
      rw [ContinuousLinearMap.map_smul, norm_smul, norm_inv, norm_norm] at h2
      have := (inv_mul_le_iff₀ hn).1 h2
      linarith
    have := ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg hM
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal this).trans (le_of_eq (ENNReal.ofReal_toReal hfin))
  refine (eLpNorm_le_of_ae_enorm_bound hWc.aestronglyMeasurable
    (Filter.Eventually.of_forall hop)).trans ?_
  simp [AVRegularity.QuietDecay.volume_unitCube_eq_one]
end

/-! The recentred block source: at a quiet time, the source of the block family (test field
centred at the moving slow point `X'`) is, for any fixed centre `X₀`, the combination
`Σ_S c_S(X') · quietSource(e_S)(X')` of the quiet sources of the fixed monomial test fields
`e_S(Y) = Π_{k∈S} (Y - X₀)_{α_k} • δ_u x`, with the polynomial weights
`c_S(X') = Π_{k∉S} (X₀ - X')_{α_k}`. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

/-- The fixed monomial test field of the sub-word `S`. -/
def subTest (u : ι) (x : h u) (X₀ : Vec 2) (β : List (Fin 2)) (S : Finset (Fin β.length)) :
    Vec 2 → ∀ i, h i :=
  fun Y => monoF X₀ (subWord β S) Y • Pi.single u x

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem contDiff_subTest (u : ι) (x : h u) (X₀ : Vec 2) (β : List (Fin 2))
    (S : Finset (Fin β.length)) : ContDiff ℝ (⊤ : ℕ∞) (subTest u x X₀ β S) :=
  (contDiff_monoF X₀ _ _).smul contDiff_const

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem blockTest_expand (u : ι) (x : h u) {m : ℕ} (α : DerivativeWord2 m) (X₀ X' : Vec 2) :
    blockTest u x α X' = fun Y => ∑ S : Finset (Fin (List.ofFn α).length),
      cS X₀ (List.ofFn α) S X' • subTest u x X₀ (List.ofFn α) S Y := by
  funext Y
  simp only [blockTest, subTest]
  rw [monoF_expand X₀ X' Y (List.ofFn α), Finset.sum_smul]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [smul_smul, mul_comm]

/-- **The recentred block source at a quiet time.** -/
theorem blockSrc_recentre {N K k L H : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    (hDsZ : D ≤ max (k + 1) (L + 2)) {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ} {qs qf : ℕ}
    {b : ι → ι → ℝ} {Θ : ℝ}
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequenceFrom Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc)
    {S : Set ℝ} (hS : S ⊆ Icc t₀ t₁) (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    {hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N) (hnq : n + 1 ≤ qs)
    {m : ℕ} (α : DerivativeWord2 m) (v u : ι) (x : h u) {σ : ℝ} (hσ : σ ∈ S) (X₀ X' z : Vec 2) :
    blockSrc Q Cc hh n α v u x σ X' z = ∑ T : Finset (Fin (List.ofFn α).length),
      cS X₀ (List.ofFn α) T X' • quietSource Q Cc (subTest u x X₀ (List.ofFn α) T) hh n σ X' z v := by
  have h1 := quiet_source N K k L D H CG Cw Cj hDsZ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf
    b Θ hset Cc hseq S hS hq (blockTest u x α X') (contDiff_blockTest u x α X') hh hhH n hn1 hnN
    σ hσ X' z
  have hf : QuietLinearFacts Q Cc σ hh n :=
    quietLinearFacts_of_setting hset hseq (by omega) hDsZ
      hS hq hσ hhH hnq
  simp only [blockSrc]
  rw [h1, blockTest_expand u x α X₀ X']
  rw [quietSource_sum Q Cc Finset.univ (fun T => cS X₀ (List.ofFn α) T X')
    (subTest u x X₀ (List.ofFn α)) (contDiff_subTest u x X₀ _) hh n σ hf X' z]
  simp only [Finset.sum_apply, Pi.smul_apply]
end

end AVRegularity.QuietDecay
end
