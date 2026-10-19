-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Coarse.Defect.FcIdent
import AVRegularity.CycleComparison.Coarse.Fact.GFBScale
import AVRegularity.CycleComparison.Coarse.Defect.DFBound
public import AVRegularity.Statements.Intermediate.CycleComparison.CoarseDefectFlux

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! The signed combination of the five families of formal adjoints making up the retained flux,
applied to the truncated response sums, and its pairing with a smooth periodic test field.

The algebraic operations of periodic Sobolev fields carry large instance terms; the combination
is assembled from the named operations `tAdd`, `tSub`, `tSum`, whose pairing identities are proved
once, so that statements about the combination stay small. -/

section
section Wrap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] {K : ℕ}

/-- The sum of two periodic Sobolev fields. -/
def tAdd (X Y : TorusHk K E) : TorusHk K E := X + Y

/-- The difference of two periodic Sobolev fields. -/
def tSub (X Y : TorusHk K E) : TorusHk K E := X - Y

/-- The sum of a finite family of periodic Sobolev fields. -/
def tSum {κ : Type*} [Fintype κ] (X : κ → TorusHk K E) : TorusHk K E := ∑ u, X u

theorem cellInner_tAdd {ψ : Vec 2 → E} (hψ : Continuous ψ) (X Y : TorusHk K E) :
    cellInner (tval (tAdd X Y)) ψ = cellInner (tval X) ψ + cellInner (tval Y) ψ :=
  cellInner_tval_add X Y hψ

theorem cellInner_tSub {ψ : Vec 2 → E} (hψ : Continuous ψ) (X Y : TorusHk K E) :
    cellInner (tval (tSub X Y)) ψ = cellInner (tval X) ψ - cellInner (tval Y) ψ :=
  cellInner_tval_sub X Y hψ

theorem cellInner_tSum {κ : Type*} [Fintype κ] {ψ : Vec 2 → E} (hψ : Continuous ψ)
    (X : κ → TorusHk K E) :
    cellInner (tval (tSum X)) ψ = ∑ u, cellInner (tval (X u)) ψ :=
  gcellInner_tval_finsetSum Finset.univ X hψ

/-- The pairing of a signed combination assembled from the named operations. -/
theorem pairing_tcombo {κ : Type*} [Fintype κ] (Y1 Y3 Y5 : TorusHk K E) (Y2 Y4 : κ → TorusHk K E)
    {ψ : Vec 2 → E} (hψ : Continuous ψ) {r1 r3 r5 : ℝ} {r2 r4 : κ → ℝ}
    (h1 : cellInner (tval Y1) ψ = r1) (h2 : ∀ u, cellInner (tval (Y2 u)) ψ = r2 u)
    (h3 : cellInner (tval Y3) ψ = r3) (h4 : ∀ u, cellInner (tval (Y4 u)) ψ = r4 u)
    (h5 : cellInner (tval Y5) ψ = r5) :
    cellInner (tval (tAdd (tSub (tAdd (tSub Y1 (tSum Y2)) Y3) (tSum Y4)) Y5)) ψ =
      (r1 - ∑ u, r2 u) + (r3 - ∑ u, r4 u) + r5 :=
  pairing_combo Y1 Y3 Y5 Y2 Y4 hψ h1 h2 h3 h4 h5

end Wrap

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The signed combination of five families of adjoints applied to five fields. -/
def adjCombo {k : ℕ} {v : ι} {m R Kc : ℕ} (hKc : k + m ≤ Kc)
    {T1 T3 T5 : (Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) → (Vec 2 → h v)}
    {T2 T4 : ∀ u, (Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) → (Vec 2 → h u)}
    {C1 C3 C5 : ℝ} {C2 C4 : ι → ℝ} (A1 : TorusAdj T1 m R Kc C1)
    (A2 : ∀ u, TorusAdj (T2 u) m R Kc (C2 u)) (A3 : TorusAdj T3 m R Kc C3)
    (A4 : ∀ u, TorusAdj (T4 u) m R Kc (C4 u)) (A5 : TorusAdj T5 m R Kc C5)
    (X1 X3 X5 : TorusHk (k + m) (h v)) (X2 X4 : ∀ u, TorusHk (k + m) (h u)) :
    TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)) :=
  tAdd (tSub (tAdd (tSub (A1.adj k hKc X1) (tSum fun u => (A2 u).adj k hKc (X2 u)))
    (A3.adj k hKc X3)) (tSum fun u => (A4 u).adj k hKc (X4 u))) (A5.adj k hKc X5)

/-- The pairing of the combination of adjoints applied to the truncated response sums. -/
theorem cellInner_adjCombo {k J H L : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)) {v : ι} {s : ℝ}
    {m R Kc : ℕ} (hKc : k + m ≤ Kc) (hm : k + m ≤ k + 2 * L)
    {T1 T3 T5 : (Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) → (Vec 2 → h v)}
    {T2 T4 : ∀ u, (Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) → (Vec 2 → h u)}
    {C1 C3 C5 : ℝ} {C2 C4 : ι → ℝ} (A1 : TorusAdj T1 m R Kc C1)
    (A2 : ∀ u, TorusAdj (T2 u) m R Kc (C2 u)) (A3 : TorusAdj T3 m R Kc C3)
    (A4 : ∀ u, TorusAdj (T4 u) m R Kc (C4 u)) (A5 : TorusAdj T5 m R Kc C5)
    {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : AVenhance.IsZ2Periodic ψ) :
    cellInner (tval (adjCombo hKc A1 A2 A3 A4 A5
        (truncateTorusHk hm (respSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s))
        (truncateTorusHk hm (respSum k J H L U ({J} ×ˢ Finset.range (H + 1)) v s))
        (truncateTorusHk hm
          (respSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range (H + 1)) v s))
        (fun u => truncateTorusHk hm
          (respSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s))
        (fun u => truncateTorusHk hm
          (respSum k J H L U (Finset.range (J + 1) ×ˢ {H}) u s)))) ψ =
      (cellInner (familyValueSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s) (T1 ψ)
        - ∑ u, cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s)
          (T2 u ψ))
      + (cellInner (familyValueSum k J H L U ({J} ×ˢ Finset.range (H + 1)) v s) (T3 ψ)
        - ∑ u, cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ {H}) u s)
          (T4 u ψ))
      + cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range (H + 1)) v s)
          (T5 ψ) := by
  have hS1 : ∀ ij ∈ Finset.range J ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hS2 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range H, ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have hS3 : ∀ ij ∈ ({J} : Finset ℕ) ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hij; omega
  have hS4 : ∀ ij ∈ Finset.range (J + 1) ×ˢ ({H} : Finset ℕ), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hij; omega
  have hS5 : ∀ ij ∈ Finset.range (J + 1) ×ˢ Finset.range (H + 1), ij.1 ≤ J ∧ ij.2 ≤ H := by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega
  have e1 := cellInner_adj_respSum (s := s) U _ hS1 A1 hKc hm hψ hp
  have e2 := fun u => cellInner_adj_respSum (s := s) U _ hS2 (A2 u) hKc hm hψ hp
  have e3 := cellInner_adj_respSum (s := s) U _ hS3 A3 hKc hm hψ hp
  have e4 := fun u => cellInner_adj_respSum (s := s) U _ hS4 (A4 u) hKc hm hψ hp
  have e5 := cellInner_adj_respSum (s := s) U _ hS5 A5 hKc hm hψ hp
  exact pairing_tcombo _ _ _ _ _ hψ.continuous e1 e2 e3 e4 e5
end

/-! The retained flux of a coarse witness is uniformly bounded on the window: it is the
combination of five formal adjoints, with constants uniform in time, applied to truncated response
sums, which are bounded since the responses are continuous on the compact window. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem norm_respSum_le {k J H L : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (S : Finset (ℕ × ℕ)) (v : ι) (s : ℝ) :
    ‖respSum k J H L U S v s‖ ≤ ∑ ij ∈ S, ‖U ij.1 ij.2 v s‖ := by
  unfold respSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ij _ => ?_)
  unfold respTrunc
  split_ifs with hle
  · exact truncateTorusHk_norm_le hle _
  · rw [norm_zero]; exact norm_nonneg _

omit [DecidableEq ι] in
/-- **The truncated response sums are bounded on the window.** -/
theorem respSum_bounded
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G) :
    ∃ MU : ℝ, 0 ≤ MU ∧ ∀ s ∈ Set.Icc t₀ t₁, ∀ w, ∀ S ⊆ cellBox J H,
      ‖respSum k J H L U S w s‖ ≤ MU := by
  have hb : ∀ ij ∈ cellBox J H, ∀ w : ι, ∃ C : ℝ, ∀ s ∈ Set.Icc t₀ t₁,
      ‖U ij.1 ij.2 w s‖ ≤ C := by
    intro ij hij w
    obtain ⟨hi, hj⟩ := mem_cellBox hij
    obtain ⟨_, _, hsol, _⟩ := hR ij.1 hi ij.2 hj
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hsol.1 w)
    exact ⟨C, hC⟩
  choose C hC using hb
  let C' : ℕ × ℕ → ι → ℝ := fun ij w => if hij : ij ∈ cellBox J H then max (C ij hij w) 0 else 0
  have hC'0 : ∀ ij w, 0 ≤ C' ij w := fun ij w => by
    simp only [C']; split_ifs <;> simp
  refine ⟨∑ ij ∈ cellBox J H, ∑ w, C' ij w, Finset.sum_nonneg fun ij _ =>
    Finset.sum_nonneg fun w _ => hC'0 ij w, fun s hs w S hS => ?_⟩
  refine (norm_respSum_le U S w s).trans ?_
  calc ∑ ij ∈ S, ‖U ij.1 ij.2 w s‖ ≤ ∑ ij ∈ S, C' ij w := Finset.sum_le_sum fun ij hij => by
        simp only [C', hS hij, ↓reduceDIte]
        exact (hC ij (hS hij) w s hs).trans (le_max_left _ _)
    _ ≤ ∑ ij ∈ cellBox J H, C' ij w :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun ij _ _ => hC'0 ij w
    _ ≤ ∑ ij ∈ cellBox J H, ∑ w', C' ij w' :=
        Finset.sum_le_sum fun ij _ => Finset.single_le_sum (f := fun w' => C' ij w')
          (fun w' _ => hC'0 ij w') (Finset.mem_univ w)

section Ops

variable (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
include P

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem fcOrd_le : k + (6 * p + D) + 1 ≤ N ∧ 6 * p + D ≤ 2 * L := by
  have hL := P.L_eq
  have hN := P.N_eq
  have h3 : 3 * L ≤ (J + H + 3) * L := Nat.mul_le_mul_right L (by omega)
  constructor <;> omega

/-- The adjoint of `F_p^*(I - 𝖰_p𝖯_p)` at a time of the window. -/
def fcT1 {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v : ι) (Bb : ℕ → ℝ)
    (hBb : ∀ l, l + 1 ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (BA : ℕ → ℕ → ℝ) (hBA : ∀ d : Finset.Icc 2 D, ∀ l, l ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l) :
    TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s
        (ψ - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p ψ))) (6 * p + D) 0
      (k + (6 * p + D))
      (fluxConstF (4 * ρ ^ 2) (commConst (4 * ρ ^ 2) (k + (6 * p + D)) Bb)
        (diagConst D (k + (6 * p + D)) BA) p *
        (1 + covPolyConst (4 * ρ ^ 2) p * covPolyConst (4 * ρ ^ 2) p)) :=
  ((TorusAdj.fluxAdj (E := h v) (covarianceMatrix Jm B t₀ s) (covBound_le P hs) b D p AD s 0
      (k + (6 * p + D)) N (by have := fcOrd_le P; have := P.p_pos; omega) (fcOrd_le P).1
      ((P.drift_smooth s hs).of_le (by exact_mod_cast le_top)) (P.drift_per s hs) Bb
      (fun l hl x => hBb l (by have := fcOrd_le P; omega) s hs x)
      (fun d => P.AD_smooth d s hs) (fun d => P.AD_per d s hs) BA
      (fun d l hl x => hBA d l (by have := fcOrd_le P; omega) s hs x)).comp
    (TorusAdj.idSubQP (E := PiLp 2 (fun _ : Fin 2 => h v)) (covarianceMatrix Jm B t₀ s)
      (covBound_le P hs) p (0 + (2 * p + D)) (k + (6 * p + D))) le_rfl le_rfl).ofOrder
    (by omega)

/-- The adjoint of `F_p^*` at a time of the window. -/
def fcT3 {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v : ι) (Bb : ℕ → ℝ)
    (hBb : ∀ l, l + 1 ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (BA : ℕ → ℕ → ℝ) (hBA : ∀ d : Finset.Icc 2 D, ∀ l, l ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l) :
    TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s ψ) (6 * p + D) 0
      (k + (6 * p + D))
      (fluxConstF (4 * ρ ^ 2) (commConst (4 * ρ ^ 2) (k + (6 * p + D)) Bb)
        (diagConst D (k + (6 * p + D)) BA) p) :=
  (TorusAdj.fluxAdj (E := h v) (covarianceMatrix Jm B t₀ s) (covBound_le P hs) b D p AD s 0
      (k + (6 * p + D)) N (by have := fcOrd_le P; have := P.p_pos; omega) (fcOrd_le P).1
      ((P.drift_smooth s hs).of_le (by exact_mod_cast le_top)) (P.drift_per s hs) Bb
      (fun l hl x => hBb l (by have := fcOrd_le P; omega) s hs x)
      (fun d => P.AD_smooth d s hs) (fun d => P.AD_per d s hs) BA
      (fun d l hl x => hBA d l (by have := fcOrd_le P; omega) s hs x)).liftOrder (by omega)

/-- The adjoint of the `(v,u)` block of `𝖯_p F_E^*` at a time of the window. -/
def fcT4 {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v u : ι) (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l, l ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (edgeExt H CE r v u d s) l x‖ ≤ BE r d.1 l) :
    TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (edgeBlock D H CE s v u ψ))
      (6 * p + D) 0 (k + (6 * p + D))
      (covPolyConst (4 * ρ ^ 2) p * edgeConst D H (k + (6 * p + D)) BE) :=
  (TorusAdj.edgeAdj (covarianceMatrix Jm B t₀ s) (covBound_le P hs) D H p CE v u s 0
      (k + (6 * p + D)) N (by have := fcOrd_le P; omega) (by have := fcOrd_le P; omega)
      (fun r hr d => P.CE_smooth r hr v u d s hs) (fun r hr d => P.CE_per r hr v u d s hs) BE
      (fun r d l hl x => hBE r d l (by have := fcOrd_le P; omega) s hs x)).liftOrder
    (by omega)

/-- The adjoint of the `(v,u)` block of `𝖯_p F_E^*(I - 𝖰_p𝖯_p)` at a time of the window. -/
def fcT2 {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v u : ι) (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l, l ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (edgeExt H CE r v u d s) l x‖ ≤ BE r d.1 l) :
    TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (edgeBlock D H CE s v u
        (ψ - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p ψ))))
      (6 * p + D) 0 (k + (6 * p + D))
      (covPolyConst (4 * ρ ^ 2) p * edgeConst D H (k + (6 * p + D)) BE *
        (1 + covPolyConst (4 * ρ ^ 2) p * covPolyConst (4 * ρ ^ 2) p)) :=
  ((TorusAdj.edgeAdj (covarianceMatrix Jm B t₀ s) (covBound_le P hs) D H p CE v u s 0
      (k + (6 * p + D)) N (by have := fcOrd_le P; omega) (by have := fcOrd_le P; omega)
      (fun r hr d => P.CE_smooth r hr v u d s hs) (fun r hr d => P.CE_per r hr v u d s hs) BE
      (fun r d l hl x => hBE r d l (by have := fcOrd_le P; omega) s hs x)).comp
    (TorusAdj.idSubQP (E := PiLp 2 (fun _ : Fin 2 => h v)) (covarianceMatrix Jm B t₀ s)
      (covBound_le P hs) p (0 + (2 * p + (D - 1))) (k + (6 * p + D))) le_rfl le_rfl).liftOrder
    (by omega)

/-- The adjoint of the Taylor operator at a time of the window, with a constant uniform in time. -/
def fcT5 {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v : ι) {Mj : ℝ}
    (hMj : ∀ t ∈ Set.Icc t₀ t₁, ∀ i j, |Jm t i j| ≤ Mj) :
    TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      taylorOp (covarianceMatrix Jm B t₀ s) p Jm B s ψ) (6 * p + D) 0 (k + (6 * p + D))
      (|((p.factorial : ℝ)⁻¹)| * ((4 * ρ ^ 2) ^ p * ∑ _k : Fin 2, ∑ _l : Fin 2,
        (Mj + |B|) * (1 * (((k + (6 * p + D)).factorial : ℝ) * 1)))) :=
  ((TorusAdj.taylor (E := h v) (covarianceMatrix Jm B t₀ s) (covBound_le P hs)
      (fun k' l => Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) p 0
      (k + (6 * p + D))).mono le_rfl le_rfl (by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
        (abs_nonneg _)
      refine Finset.sum_le_sum fun k' _ => Finset.sum_le_sum fun l _ => ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine (abs_sub _ _).trans (add_le_add (hMj s hs k' l) ?_)
      rw [abs_mul]
      refine mul_le_of_le_one_right (abs_nonneg B) ?_
      by_cases hkl : k' = l
      · rw [hkl, Matrix.one_apply_eq, abs_one]
      · rw [Matrix.one_apply_ne hkl, abs_zero]; exact zero_le_one)).liftOrder
    (by have := P.D_ge; omega)

end Ops

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem norm_adj_trunc_le {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
    {T : (Vec 2 → F) → (Vec 2 → E)} {m R Kc K₀ K' : ℕ} {C : ℝ} (A : TorusAdj T m R Kc C)
    (hKc : K₀ + m ≤ Kc) (hm : K₀ + m ≤ K') (X : TorusHk K' E) {MU : ℝ} (hX : ‖X‖ ≤ MU) :
    ‖A.adj K₀ hKc (truncateTorusHk hm X)‖ ≤ C * MU :=
  ((A.adj K₀ hKc).le_opNorm _).trans (mul_le_mul (A.bound K₀ hKc)
    ((truncateTorusHk_norm_le hm X).trans hX) (norm_nonneg _)
    ((norm_nonneg (A.adj K₀ hKc)).trans (A.bound K₀ hKc)))
end

/-! Regularity of the test operators of the coarse fluxes at a time of the window, read off from
their formal adjoints: on smooth periodic fields they produce continuous periodic fields, of class
`C^{2p}` when needed. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

section
variable (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
include P

/-- `F_p(s)^*` maps smooth periodic fields to continuous periodic fields. -/
theorem fluxAdj_regular {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v : ι)
    {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : AVenhance.IsZ2Periodic ψ) :
    Continuous (AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s ψ) ∧
      AVenhance.IsZ2Periodic
        (AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s ψ) := by
  obtain ⟨Bb, hBb⟩ := exists_drift_bounds P
  obtain ⟨BA, hBA⟩ := exists_diag_bounds P
  have hm := (fcT3 P hs v Bb hBb BA hBA).maps 0 le_rfl ψ
    (hψ.of_le (WithTop.coe_le_coe.mpr le_top)) hp
  exact ⟨hm.1.continuous, hm.2⟩

/-- The `(v,u)` block of `𝖯_p F_E(s)^*` maps smooth periodic fields to continuous periodic
fields. -/
theorem edgeAdj_regular {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v u : ι)
    {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : AVenhance.IsZ2Periodic ψ) :
    Continuous (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
        (edgeBlock D H CE s v u ψ)) ∧
      AVenhance.IsZ2Periodic (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
        (edgeBlock D H CE s v u ψ)) := by
  obtain ⟨BE, hBE⟩ := exists_edge_bounds P
  have hm := (fcT4 P hs v u (BE v u) (hBE v u)).maps 0 le_rfl ψ
    (hψ.of_le (WithTop.coe_le_coe.mpr le_top)) hp
  exact ⟨hm.1.continuous, hm.2⟩

/-- The diagonal flux adjoint maps smooth periodic fields to `C^{2p}` periodic fields. -/
theorem diagFlux_regular {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v : ι)
    {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : AVenhance.IsZ2Periodic ψ) :
    ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) (AVRegularity.diagonalFluxAdjoint D AD s ψ) ∧
      AVenhance.IsZ2Periodic (AVRegularity.diagonalFluxAdjoint D AD s ψ) := by
  obtain ⟨BA, hBA⟩ := exists_diag_bounds P
  have hL := P.L_eq
  have hord := fcOrd_le P
  have hm := (TorusAdj.diagFlux (E := h v) D AD s (2 * p) k N (by omega) (by omega)
    (fun d => P.AD_smooth d s hs) (fun d => P.AD_per d s hs) BA
    (fun d l hl x => hBA d l (by omega) s hs x)).maps (2 * p) le_rfl ψ
    (hψ.of_le (WithTop.coe_le_coe.mpr le_top)) hp
  exact hm

/-- The `(v,u)` edge block maps smooth periodic fields to `C^{2p}` periodic fields. -/
theorem edgeBlock_regular {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v u : ι)
    {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : AVenhance.IsZ2Periodic ψ) :
    ContDiff ℝ ((2 * p : ℕ) : WithTop ℕ∞) (edgeBlock D H CE s v u ψ) ∧
      AVenhance.IsZ2Periodic (edgeBlock D H CE s v u ψ) := by
  obtain ⟨BE, hBE⟩ := exists_edge_bounds P
  have hL := P.L_eq
  have hord := fcOrd_le P
  have hm := (TorusAdj.edgeFluxBlock (X := h v) (Y := h u) D H
    (fun r d => edgeExt H CE r v u d s) (2 * p) k N (by omega) (by omega)
    (fun r d => by
      by_cases hr : r ∈ Finset.Icc 1 H
      · rw [edgeExt_of_mem hr]; exact P.CE_smooth r hr v u d s hs
      · have he : edgeExt (D := D) H CE r v u d s = 0 := by simp [edgeExt, hr]
        rw [he]; exact contDiff_const)
    (fun r d => by
      by_cases hr : r ∈ Finset.Icc 1 H
      · rw [edgeExt_of_mem hr]; exact P.CE_per r hr v u d s hs
      · have he : edgeExt (D := D) H CE r v u d s = 0 := by simp [edgeExt, hr]
        rw [he]; intro n x; rfl)
    (BE v u) (fun r d l hl x => hBE v u r d l (by omega) s hs x)).maps (2 * p) le_rfl ψ
    (hψ.of_le (WithTop.coe_le_coe.mpr le_top)) hp
  have e : (fun x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
      AVRegularity.wordAdjoint (d.1 - 1)
        (fun y => ContinuousLinearMap.adjoint (edgeExt H CE r v u d s y) (ψ y)) x) =
      edgeBlock D H CE s v u ψ := by
    funext x
    unfold edgeBlock
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun d _ => ?_
    simp only [edgeExt_of_mem hr]
  rw [e] at hm
  exact hm

end
end

/-! The uniform bound of the retained flux of a coarse witness on the window. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

/-- The norm of a signed combination. -/
theorem norm_combo_le {X : Type*} [SeminormedAddCommGroup X] {κ : Type*} [Fintype κ]
    {x1 x3 x5 : X} {x2 x4 : κ → X} {c1 c3 c5 : ℝ} {c2 c4 : κ → ℝ} (h1 : ‖x1‖ ≤ c1)
    (h2 : ∀ u, ‖x2 u‖ ≤ c2 u) (h3 : ‖x3‖ ≤ c3) (h4 : ∀ u, ‖x4 u‖ ≤ c4 u) (h5 : ‖x5‖ ≤ c5) :
    ‖x1 - ∑ u, x2 u + x3 - ∑ u, x4 u + x5‖ ≤ c1 + ∑ u, c2 u + c3 + ∑ u, c4 u + c5 := by
  have hs2 : ‖∑ u, x2 u‖ ≤ ∑ u, c2 u := (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => h2 u)
  have hs4 : ‖∑ u, x4 u‖ ≤ ∑ u, c4 u := (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => h4 u)
  calc ‖x1 - ∑ u, x2 u + x3 - ∑ u, x4 u + x5‖
      ≤ ‖x1 - ∑ u, x2 u + x3 - ∑ u, x4 u‖ + ‖x5‖ := norm_add_le _ _
    _ ≤ (‖x1 - ∑ u, x2 u + x3‖ + ‖∑ u, x4 u‖) + ‖x5‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((‖x1 - ∑ u, x2 u‖ + ‖x3‖) + ‖∑ u, x4 u‖) + ‖x5‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (((‖x1‖ + ‖∑ u, x2 u‖) + ‖x3‖) + ‖∑ u, x4 u‖) + ‖x5‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ c1 + ∑ u, c2 u + c3 + ∑ u, c4 u + c5 := by gcongr

/-- The operator constant of the retained flux of component `v`. -/
def fcConst (ρ B : ℝ) (k p D H : ℕ) (Bb : ℕ → ℝ) (BA : ℕ → ℕ → ℝ)
    (BE : ι → ι → ℕ → ℕ → ℕ → ℝ) (Mj : ℝ) (v : ι) : ℝ :=
  fluxConstF (4 * ρ ^ 2) (commConst (4 * ρ ^ 2) (k + (6 * p + D)) Bb)
      (diagConst D (k + (6 * p + D)) BA) p *
      (1 + covPolyConst (4 * ρ ^ 2) p * covPolyConst (4 * ρ ^ 2) p)
    + ∑ u, covPolyConst (4 * ρ ^ 2) p * edgeConst D H (k + (6 * p + D)) (BE v u) *
      (1 + covPolyConst (4 * ρ ^ 2) p * covPolyConst (4 * ρ ^ 2) p)
    + fluxConstF (4 * ρ ^ 2) (commConst (4 * ρ ^ 2) (k + (6 * p + D)) Bb)
      (diagConst D (k + (6 * p + D)) BA) p
    + ∑ u, covPolyConst (4 * ρ ^ 2) p * edgeConst D H (k + (6 * p + D)) (BE v u)
    + |((p.factorial : ℝ)⁻¹)| * ((4 * ρ ^ 2) ^ p * ∑ _k : Fin 2, ∑ _l : Fin 2,
      (Mj + |B|) * (1 * (((k + (6 * p + D)).factorial : ℝ) * 1)))

/-- The retained flux at one time, bounded through five abstract adjoints. -/
private theorem witness_Fc_norm_le_of_adj
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))} {Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm Hcov U W Fc)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v : ι) {m R Kc : ℕ} (hKc : k + m ≤ Kc)
    (hm : k + m ≤ k + 2 * L) {C1 C3 C5 : ℝ} {C2 C4 : ι → ℝ}
    (T1 : TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.coarseFluxAdjoint D b AD (Hcov s) p s
        (ψ - AVRegularity.covPolyQ (Hcov s) p (AVRegularity.covPolyP (Hcov s) p ψ))) m R Kc C1)
    (T2 : ∀ u, TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP (Hcov s) p (edgeBlock D H CE s v u
        (ψ - AVRegularity.covPolyQ (Hcov s) p (AVRegularity.covPolyP (Hcov s) p ψ))))
      m R Kc (C2 u))
    (T3 : TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.coarseFluxAdjoint D b AD (Hcov s) p s ψ) m R Kc C3)
    (T4 : ∀ u, TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP (Hcov s) p (edgeBlock D H CE s v u ψ)) m R Kc (C4 u))
    (T5 : TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      taylorOp (Hcov s) p Jm B s ψ) m R Kc C5) {MU : ℝ}
    (hS1 : ‖respSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s‖ ≤ MU)
    (hS2 : ∀ u, ‖respSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s‖ ≤ MU)
    (hS3 : ‖respSum k J H L U ({J} ×ˢ Finset.range (H + 1)) v s‖ ≤ MU)
    (hS4 : ∀ u, ‖respSum k J H L U (Finset.range (J + 1) ×ˢ {H}) u s‖ ≤ MU)
    (hS5 : ‖respSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range (H + 1)) v s‖ ≤ MU) :
    ‖Fc v s‖ ≤ C1 * MU + ∑ u, C2 u * MU + C3 * MU + ∑ u, C4 u * MU + C5 * MU := by
  rw [witness_Fc_eq_of_adj hWit hs v hKc hm T1 T2 T3 T4 T5]
  exact norm_combo_le (norm_adj_trunc_le T1 hKc hm _ hS1)
    (fun u => norm_adj_trunc_le (T2 u) hKc hm _ (hS2 u)) (norm_adj_trunc_le T3 hKc hm _ hS3)
    (fun u => norm_adj_trunc_le (T4 u) hKc hm _ (hS4 u)) (norm_adj_trunc_le T5 hKc hm _ hS5)

/-- **The retained flux at one time.** -/
theorem witness_Fc_norm_le
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc)
    (Bb : ℕ → ℝ)
    (hBb : ∀ l, l + 1 ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (BA : ℕ → ℕ → ℝ) (hBA : ∀ d : Finset.Icc 2 D, ∀ l, l ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l)
    (BE : ι → ι → ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ v u r (d : Finset.Icc 2 D), ∀ l, l ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (edgeExt H CE r v u d s) l x‖ ≤ BE v u r d.1 l)
    {Mj : ℝ} (hMj : ∀ t ∈ Set.Icc t₀ t₁, ∀ i j, |Jm t i j| ≤ Mj) {MU : ℝ}
    (hMU : ∀ s ∈ Set.Icc t₀ t₁, ∀ w, ∀ S ⊆ cellBox J H, ‖respSum k J H L U S w s‖ ≤ MU)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (v : ι) :
    ‖Fc v s‖ ≤ fcConst ρ B k p D H Bb BA BE Mj v * MU := by
  have hm : k + (6 * p + D) ≤ k + 2 * L := by have := (fcOrd_le P).2; omega
  have hsub : ∀ {S : Finset (ℕ × ℕ)}, (∀ ij ∈ S, ij.1 ≤ J ∧ ij.2 ≤ H) → S ⊆ cellBox J H :=
    fun hS ij hij => by
      have := hS ij hij
      simp only [cellBox, Finset.mem_product, Finset.mem_range]; omega
  have hS1 := hMU s hs v _ (hsub (S := Finset.range J ×ˢ Finset.range (H + 1)) (by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega))
  have hS3 := hMU s hs v _ (hsub (S := ({J} : Finset ℕ) ×ˢ Finset.range (H + 1)) (by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hij; omega))
  have hS5 := hMU s hs v _ (hsub (S := Finset.range (J + 1) ×ˢ Finset.range (H + 1)) (by
    intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega))
  have hS2 : ∀ u, ‖respSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s‖ ≤ MU :=
    fun u => hMU s hs u _ (hsub (by
      intro ij hij; simp only [Finset.mem_product, Finset.mem_range] at hij; omega))
  have hS4 : ∀ u, ‖respSum k J H L U (Finset.range (J + 1) ×ˢ ({H} : Finset ℕ)) u s‖ ≤ MU :=
    fun u => hMU s hs u _ (hsub (by
      intro ij hij
      simp only [Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hij; omega))
  refine (witness_Fc_norm_le_of_adj hWit hs v (le_refl _) hm (fcT1 P hs v Bb hBb BA hBA)
    (fun u => fcT2 P hs v u (BE v u) (hBE v u)) (fcT3 P hs v Bb hBb BA hBA)
    (fun u => fcT4 P hs v u (BE v u) (hBE v u)) (fcT5 P hs v hMj) hS1 hS2 hS3 hS4 hS5).trans
    (le_of_eq ?_)
  unfold fcConst
  simp only [add_mul, Finset.sum_mul]

/-- **The retained flux of a witness is uniformly bounded on the window.** -/
theorem witness_Fc_bounded
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc) :
    ∃ M : ℝ, ∀ s ∈ Set.Icc t₀ t₁, ∀ v, ‖Fc v s‖ ≤ M := by
  obtain ⟨Bb, hBb⟩ := exists_drift_bounds P
  obtain ⟨BA, hBA⟩ := exists_diag_bounds P
  obtain ⟨BE, hBE⟩ := exists_edge_bounds P
  obtain ⟨Mj, hMj⟩ := jm_bound P
  obtain ⟨MU, -, hMU⟩ := respSum_bounded hR
  refine ⟨∑ v, |fcConst ρ B k p D H Bb BA BE Mj v * MU|, fun s hs v => ?_⟩
  exact (witness_Fc_norm_le P hWit Bb hBb BA hBA BE hBE hMj hMU hs v).trans
    ((le_abs_self _).trans (Finset.single_le_sum (f := fun v =>
      |fcConst ρ B k p D H Bb BA BE Mj v * MU|) (fun v _ => abs_nonneg _) (Finset.mem_univ v)))
end

/-! **The coarse witness exists**. The retained field is the
`𝖯_p`-adjoint of the total response, and the retained flux is the combination of the five formal
adjoints of the parts of the dual expression applied to the truncated response sums. The flux
identity holds one source component at a time by construction; for a family of tests the edge
pairings add up over the source components. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem memLp_familyValueSum {k J H L : ℕ}
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (S : Finset (ℕ × ℕ)) (v : ι) (s : ℝ) :
    MemLp (familyValueSum k J H L U S v s) 2 (volume.restrict AVenhance.unitCube) :=
  memLp_finsetSum S fun ij _ => memLp_tval (U ij.1 ij.2 v s)

/-- The signed combination of the edge and Taylor pairings, summed over the components. -/
theorem sum_combo_swap {κ : Type*} [Fintype κ] (a c e : κ → ℝ) (r2 r4 : κ → κ → ℝ) :
    ∑ v, ((a v - ∑ u, r2 v u) + (c v - ∑ u, r4 v u) + e v) =
      (∑ v, a v - ∑ u, ∑ v, r2 v u) + (∑ v, c v - ∑ u, ∑ v, r4 v u) + ∑ v, e v := by
  rw [Finset.sum_comm (f := fun u v => r2 v u), Finset.sum_comm (f := fun u v => r4 v u)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem combo_congr {a c e x y x' y' : ℝ} (hx : x = x') (hy : y = y') :
    (a - x) + (c - y) + e = (a - x') + (c - y') + e := by
  rw [hx, hy]

section Cand

variable (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
include P

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem fc_trunc_le : k + (6 * p + D) ≤ k + 2 * L := by
  have := (fcOrd_le P).2
  omega

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem retained_ord_le : k + 1 + D + 2 * p ≤ k + 2 * L := by
  have := P.L_eq
  omega

/-- The candidate retained flux at a time of the window. -/
def candFcAt (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (Bb : ℕ → ℝ)
    (hBb : ∀ l, l + 1 ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (BA : ℕ → ℕ → ℝ) (hBA : ∀ d : Finset.Icc 2 D, ∀ l, l ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l)
    (BE : ι → ι → ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ v u r (d : Finset.Icc 2 D), ∀ l, l ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (edgeExt H CE r v u d s) l x‖ ≤ BE v u r d.1 l)
    {Mj : ℝ} (hMj : ∀ t ∈ Set.Icc t₀ t₁, ∀ i j, |Jm t i j| ≤ Mj) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) (v : ι) : TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)) :=
  adjCombo le_rfl (fcT1 P hs v Bb hBb BA hBA) (fun u => fcT2 P hs v u (BE v u) (hBE v u))
    (fcT3 P hs v Bb hBb BA hBA) (fun u => fcT4 P hs v u (BE v u) (hBE v u)) (fcT5 P hs v hMj)
    (truncateTorusHk (fc_trunc_le P)
      (respSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s))
    (truncateTorusHk (fc_trunc_le P) (respSum k J H L U ({J} ×ˢ Finset.range (H + 1)) v s))
    (truncateTorusHk (fc_trunc_le P)
      (respSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range (H + 1)) v s))
    (fun u => truncateTorusHk (fc_trunc_le P)
      (respSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s))
    (fun u => truncateTorusHk (fc_trunc_le P)
      (respSum k J H L U (Finset.range (J + 1) ×ˢ {H}) u s))

/-- **The candidate retained flux** (zero off the window). -/
def candFc (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (Bb : ℕ → ℝ)
    (hBb : ∀ l, l + 1 ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (BA : ℕ → ℕ → ℝ) (hBA : ∀ d : Finset.Icc 2 D, ∀ l, l ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l)
    (BE : ι → ι → ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ v u r (d : Finset.Icc 2 D), ∀ l, l ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (edgeExt H CE r v u d s) l x‖ ≤ BE v u r d.1 l)
    {Mj : ℝ} (hMj : ∀ t ∈ Set.Icc t₀ t₁, ∀ i j, |Jm t i j| ≤ Mj) (v : ι) (s : ℝ) :
    TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)) :=
  if hs : s ∈ Set.Icc t₀ t₁ then candFcAt P U Bb hBb BA hBA BE hBE hMj hs v else 0

theorem candFc_eq (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (Bb : ℕ → ℝ)
    (hBb : ∀ l, l + 1 ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (BA : ℕ → ℕ → ℝ) (hBA : ∀ d : Finset.Icc 2 D, ∀ l, l ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l)
    (BE : ι → ι → ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ v u r (d : Finset.Icc 2 D), ∀ l, l ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (edgeExt H CE r v u d s) l x‖ ≤ BE v u r d.1 l)
    {Mj : ℝ} (hMj : ∀ t ∈ Set.Icc t₀ t₁, ∀ i j, |Jm t i j| ≤ Mj) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) (v : ι) :
    candFc P U Bb hBb BA hBA BE hBE hMj v s = candFcAt P U Bb hBb BA hBA BE hBE hMj hs v :=
  dite_eq_left hs

/-- The candidate retained flux satisfies the flux identity one component at a time. -/
theorem cellInner_candFc (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (Bb : ℕ → ℝ)
    (hBb : ∀ l, l + 1 ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (BA : ℕ → ℕ → ℝ) (hBA : ∀ d : Finset.Icc 2 D, ∀ l, l ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l)
    (BE : ι → ι → ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ v u r (d : Finset.Icc 2 D), ∀ l, l ≤ N → ∀ s ∈ Set.Icc t₀ t₁, ∀ x,
      ‖coefficientDerivativeArray (edgeExt H CE r v u d s) l x‖ ≤ BE v u r d.1 l)
    {Mj : ℝ} (hMj : ∀ t ∈ Set.Icc t₀ t₁, ∀ i j, |Jm t i j| ≤ Mj) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) (v : ι) {ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    cellInner (tval (candFc P U Bb hBb BA hBA BE hBE hMj v s)) ψ =
      (cellInner (familyValueSum k J H L U (Finset.range J ×ˢ Finset.range (H + 1)) v s)
          (AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s
            (ψ - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
              (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p ψ)))
        - ∑ u, cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range H) u s)
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (edgeBlock D H CE s v u
            (ψ - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
              (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p ψ)))))
      + (cellInner (familyValueSum k J H L U ({J} ×ˢ Finset.range (H + 1)) v s)
          (AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s ψ)
        - ∑ u, cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ {H}) u s)
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (edgeBlock D H CE s v u ψ)))
      + cellInner (familyValueSum k J H L U (Finset.range (J + 1) ×ˢ Finset.range (H + 1)) v s)
          (taylorOp (covarianceMatrix Jm B t₀ s) p Jm B s ψ) := by
  rw [candFc_eq P U Bb hBb BA hBA BE hBE hMj hs v]
  exact cellInner_adjCombo U le_rfl (fc_trunc_le P) (fcT1 P hs v Bb hBb BA hBA)
    (fun u => fcT2 P hs v u (BE v u) (hBE v u)) (fcT3 P hs v Bb hBb BA hBA)
    (fun u => fcT4 P hs v u (BE v u) (hBE v u)) (fcT5 P hs v hMj) hψ hp

/-- The edge pairings of a family of tests add up over the source components. -/
theorem edge_family_sum {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (S : Finset (ℕ × ℕ))
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (χ : ∀ v, Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) (hχ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (χ v))
    (hχp : ∀ v, AVenhance.IsZ2Periodic (χ v)) :
    ∑ u, ∑ v, cellInner (familyValueSum k J H L U S u s)
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (edgeBlock D H CE s v u (χ v))) =
      ∑ u, cellInner (familyValueSum k J H L U S u s)
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
          (AVRegularity.edgeFluxAdjoint D H CE s χ u)) := by
  have hreg := fun v u => edgeBlock_regular P hs v u (hχ v) (hχp v)
  have hcont : ∀ v u, Continuous (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p
      (edgeBlock D H CE s v u (χ v))) := fun v u =>
    ((TorusAdj.covPolyP (E := h u) (covarianceMatrix Jm B t₀ s) le_rfl p 0 0).maps 0 le_rfl _
      (by simpa using (hreg v u).1) (hreg v u).2).1.continuous
  refine (edge_pairing_sum (covarianceMatrix Jm B t₀ s) p
    (fun v u => edgeBlock D H CE s v u (χ v)) (fun v u => by simpa using (hreg v u).1) hcont
    (fun u => familyValueSum k J H L U S u s) (fun u => memLp_familyValueSum U S u s)).trans ?_
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [edgeFluxAdjoint_eq_sum]
  rfl

end Cand

/-- **The coarse witness exists.** -/
theorem exists_coarse_witness
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)) :
    ∃ (W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v))
      (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))),
      IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc := by
  obtain ⟨Bb, hBb⟩ := exists_drift_bounds P
  obtain ⟨BA, hBA⟩ := exists_diag_bounds P
  obtain ⟨BE, hBE⟩ := exists_edge_bounds P
  obtain ⟨Mj, hMj⟩ := jm_bound P
  refine ⟨retainedW k J H L p D (covarianceMatrix Jm B t₀) U (retained_ord_le P),
    candFc P U Bb hBb BA hBA BE hBE hMj, ?_, ?_⟩
  · intro t ht φ hφ hp
    refine Finset.sum_congr rfl fun v _ => ?_
    exact cellInner_retainedW _ U (retained_ord_le P) v t
      ((hφ v).of_le (WithTop.coe_le_coe.mpr le_top)) (hp v)
  · intro s hs ψ hψ hp
    have hχ : ∀ v, ContDiff ℝ (⊤ : ℕ∞)
        (ψ v - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (ψ v))) := fun v =>
      (hψ v).sub (contDiff_covPolyQ_top (covarianceMatrix Jm B t₀ s) p
        (contDiff_covPolyP_top (covarianceMatrix Jm B t₀ s) p (hψ v)))
    have hχp : ∀ v, AVenhance.IsZ2Periodic
        (ψ v - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (ψ v))) := fun v n x => by
      have h1 := hp v n x
      have h2 := isZ2Periodic_covPolyQ (covarianceMatrix Jm B t₀ s) p
        (contDiff_covPolyP_top (covarianceMatrix Jm B t₀ s) p (hψ v))
        (isZ2Periodic_covPolyP (covarianceMatrix Jm B t₀ s) p (hψ v) (hp v)) n x
      simp only [Pi.sub_apply, h1, h2]
    have e1 : ∑ v, cellInner (fun x => (candFc P U Bb hBb BA hBA BE hBE hMj v s).toFunction.jet
        (valueIndex2 k) x) (ψ v) = _ :=
      Finset.sum_congr rfl fun v _ => cellInner_candFc P U Bb hBb BA hBA BE hBE hMj hs v (hψ v)
        (hp v)
    exact (e1.trans (sum_combo_swap _ _ _ _ _)).trans (combo_congr
      (edge_family_sum P hs _ U (fun v => ψ v - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
        (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (ψ v))) hχ hχp)
      (edge_family_sum P hs _ U ψ hψ hp))
end

/-! The retained field of a coarse witness is uniformly bounded on the window. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

omit [Fintype ι] [DecidableEq ι] in
/-- The candidate retained field is bounded by the covariance polynomial constant. -/
theorem norm_retainedW_le {k J H L p D : ℕ} (Hcov : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (hord : k + 1 + D + 2 * p ≤ k + 2 * L) (v : ι) (t : ℝ) :
    ‖retainedW k J H L p D Hcov U hord v t‖ ≤
      covPolyConst (covBound (Hcov t)) p * ‖respSum k J H L U (cellBox J H) v t‖ := by
  unfold retainedW
  refine (truncateTorusHk_norm_le _ _).trans ?_
  refine ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
    ((TorusAdj.covPolyP (E := h v) (Hcov t) le_rfl p 0 (k + 2 * L)).bound _ _)
    (norm_nonneg _))).trans (le_of_eq ?_)
  rw [norm_torusCast]

/-- **The retained field of a witness is uniformly bounded on the window.** -/
theorem witness_W_bounded
    (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
    {f : ∀ v, TorusHk N (h v)}
    {U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v)}
    {Uw : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j + 1) (h v)}
    {G : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j)
      (PiLp 2 (fun _ : Fin 2 => h v))}
    (hR : IsCoarseResponses t₀ t₁ B b D H p k J L N AD CE (covarianceMatrix Jm B t₀) f U Uw G)
    {W : ∀ v, ℝ → TorusHk (k + 1 + D) (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    (hWit : IsCoarseWitness t₀ t₁ B b D H p k J L AD CE Jm (covarianceMatrix Jm B t₀) U W Fc) :
    ∃ MW : ℝ, ∀ s ∈ Set.Icc t₀ t₁, ∀ v, ‖W v s‖ ≤ MW := by
  obtain ⟨MU, hMU0, hMU⟩ := respSum_bounded hR
  have hord : k + 1 + D + 2 * p ≤ k + 2 * L := by have := P.L_eq; omega
  refine ⟨covPolyConst (4 * ρ ^ 2) p * MU, fun s hs v => ?_⟩
  rw [witness_W_eq (covarianceMatrix Jm B t₀) U W hWit.1 hord hs v]
  refine (norm_retainedW_le _ U hord v s).trans ?_
  exact mul_le_mul (gfbCovPoly_mono (covBound_nonneg _) (covBound_le P hs) p)
    (hMU s hs v _ le_rfl) (norm_nonneg _)
    ((Finset.sum_nonneg fun l _ => by positivity : (0 : ℝ) ≤ covPolyConst (4 * ρ ^ 2) p))
end

/-! The witness side of the conjugation identity at one time: the right side of the weak
identity of the retained field `W`, tested with a smooth periodic field `ψ`, written through the
response sums: `(A, 𝖯_p(b·∇ψ)) + B(A, 𝖯_pΔψ) + (A, 𝖯_p 𝒞'ψ) - (A, 𝖯_p F_A^*∇ψ)
- ∑_u (A_u, 𝖯_p (F_E^*∇ψ)_u) - (F_coarse, ∇ψ)`. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The integrand of the weak identity of the retained field, tested with `ψ` (without the
vanishing source term). -/
def wIntegrand {K₀ : ℕ} (B : ℝ) (b : ℝ → Vec 2 → Vec 2) (D H : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (Fc : ∀ v, ℝ → TorusHk K₀ (PiLp 2 (fun _ : Fin 2 => h v))) (v : ι) (ψ : Vec 2 → h v)
    (s : ℝ) (x : Vec 2) : ℝ :=
  -(∑ k : Fin 2, b s x k * inner ℝ (torusJetOrder (W v s) 1 (fun _ => k) x) (ψ x))
    - B * ∑ k : Fin 2, inner ℝ (torusJetOrder (W v s) 1 (fun _ => k) x)
      (fderiv ℝ ψ x (basisVec k))
    - ∑ k : Fin 2, inner ℝ (AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x k +
        (Fc v s).toFunction.jet (valueIndex2 K₀) x k) (fderiv ℝ ψ x (basisVec k))

/-- The test operator `𝒞'ψ = ∑_{k,l} (𝖩(s) - B I)_{kl} ∂_l ∂_k ψ`. -/
def rateOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (B s : ℝ) (ψ : Vec 2 → E) : Vec 2 → E :=
  fun x => ∑ k : Fin 2, ∑ l : Fin 2, (Jm s k l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k l) •
    fderiv ℝ (fun y => fderiv ℝ ψ y (basisVec k)) x (basisVec l)

omit [DecidableEq ι] in
/-- **The pairing form of the retained-field integrand.** -/
theorem integral_wIntegrand {K₀ : ℕ} {B : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (Fc : ∀ v, ℝ → TorusHk K₀ (PiLp 2 (fun _ : Fin 2 => h v))) (hDK : D ≤ K + 1) (hK : 1 ≤ K)
    (hD1 : 1 ≤ D) (v : ι) {s : ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) (b s)) (hbp : AVenhance.IsZ2Periodic (b s))
    (hdiv : ∀ x, ∑ k : Fin 2, fderiv ℝ (b s) x (basisVec k) k = 0)
    (hA : ∀ d, ContDiff ℝ (D : WithTop ℕ∞) (AD d s)) (hAp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (hC : ∀ r ∈ Finset.Icc 1 H, ∀ u d, ContDiff ℝ (D : WithTop ℕ∞) (CE r v u d s))
    (hCp : ∀ r ∈ Finset.Icc 1 H, ∀ u d, AVenhance.IsZ2Periodic (CE r v u d s))
    {ψ : Vec 2 → h v} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    Integrable (wIntegrand B b D H AD CE Jm W Fc v ψ s) (volume.restrict AVenhance.unitCube) ∧
      ∫ x in AVenhance.unitCube, wIntegrand B b D H AD CE Jm W Fc v ψ s x =
        cellInner (tval (W v s)) (driftDeriv (b s) ψ)
          + B * cellInner (tval (W v s)) (lapField ψ)
          + cellInner (tval (W v s)) (rateOp Jm B s ψ)
          - cellInner (tval (W v s)) (AVRegularity.diagonalFluxAdjoint D AD s (gradField ψ))
          - ∑ u, cellInner (tval (W u s)) (edgeBlock D H CE s v u (gradField ψ))
          - cellInner (tval (Fc v s)) (gradField ψ) := by
  have hb1 : ContDiff ℝ 1 (b s) := hb.of_le (by exact_mod_cast le_top)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
  have hψ2 : ContDiff ℝ 2 ψ := by simpa using contDiff_top_nat hψ 2
  have hg : ContDiff ℝ (D : WithTop ℕ∞) (gradField ψ) :=
    (contDiff_gradField_top hψ).of_le (by exact_mod_cast le_top)
  have hgp : AVenhance.IsZ2Periodic (gradField ψ) := isZ2Periodic_gradField hψ hp
  obtain ⟨i1, e1⟩ := integral_drift_jet (W v s) hK hb1 hbp hdiv hψ1 hp
  obtain ⟨i2, e2⟩ := integral_diffusion_jet (W v s) hK hψ2 hp
  obtain ⟨i3, e3⟩ := cellInner_coarseDefectFlux B AD CE Jm W hDK hK hD1 v s hA hAp hC hCp hg hgp
  have hFc : MemLp (fun x => (Fc v s).toFunction.jet (valueIndex2 K₀) x) 2
      (volume.restrict AVenhance.unitCube) := (Fc v s).toFunction.hasPeriodicWeakJet.2.1 _
  have i4 : Integrable (fun x => inner ℝ ((Fc v s).toFunction.jet (valueIndex2 K₀) x)
      (gradField ψ x)) (volume.restrict AVenhance.unitCube) :=
    integrable_inner_continuous hFc (contDiff_gradField_top hψ).continuous
  have hpt : ∀ x, wIntegrand B b D H AD CE Jm W Fc v ψ s x =
      -(∑ k : Fin 2, b s x k * inner ℝ (torusJetOrder (W v s) 1 (fun _ => k) x) (ψ x))
        - B * ∑ k : Fin 2, inner ℝ (torusJetOrder (W v s) 1 (fun _ => k) x)
          (fderiv ℝ ψ x (basisVec k))
        - (inner ℝ (AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x) (gradField ψ x)
          + inner ℝ ((Fc v s).toFunction.jet (valueIndex2 K₀) x) (gradField ψ x)) := fun x => by
    unfold wIntegrand
    congr 1
    rw [PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_add_left]
    rfl
  have hI : Integrable (fun x => -(∑ k : Fin 2, b s x k *
      inner ℝ (torusJetOrder (W v s) 1 (fun _ => k) x) (ψ x))
        - B * ∑ k : Fin 2, inner ℝ (torusJetOrder (W v s) 1 (fun _ => k) x)
          (fderiv ℝ ψ x (basisVec k))
        - (inner ℝ (AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x) (gradField ψ x)
          + inner ℝ ((Fc v s).toFunction.jet (valueIndex2 K₀) x) (gradField ψ x)))
      (volume.restrict AVenhance.unitCube) :=
    (i1.neg.sub (i2.const_mul B)).sub (i3.add i4)
  refine ⟨hI.congr (ae_of_all _ fun x => (hpt x).symm), ?_⟩
  have h1 := integral_sub (i1.neg.sub (i2.const_mul B)) (i3.add i4)
  have h2 := integral_sub i1.neg (i2.const_mul B)
  have h3 := integral_add i3 i4
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply] at h1 h2 h3
  rw [integral_congr_ae (ae_of_all _ hpt), h1, h2, integral_neg, integral_const_mul, h3, e1, e2]
  change -(-cellInner (tval (W v s)) (driftDeriv (b s) ψ)) -
      B * -cellInner (tval (W v s)) (lapField ψ) -
      (cellInner (fun x => AVRegularity.coarseDefectFlux B D H AD CE Jm W v s x) (gradField ψ) +
        cellInner (tval (Fc v s)) (gradField ψ)) = _
  rw [e3]
  have hrate : (fun x => ∑ k : Fin 2, ∑ l : Fin 2,
      (Jm s k l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k l) •
        fderiv ℝ (fun y => gradField ψ y k) x (basisVec l)) = rateOp Jm B s ψ := by
    funext x
    rfl
  rw [hrate]
  have hdiag : (fun x => ∑ d : Finset.Icc 2 D, AVRegularity.wordAdjoint (d.1 - 1)
      (fun y => AVRegularity.tensorFluxAdjoint (AD d s y) (gradField ψ y)) x) =
      AVRegularity.diagonalFluxAdjoint D AD s (gradField ψ) := rfl
  rw [hdiag]
  have hedge : ∀ u, (fun x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
      AVRegularity.wordAdjoint (d.1 - 1)
        (fun y => ContinuousLinearMap.adjoint (CE r v u d s y) (gradField ψ y)) x) =
      edgeBlock D H CE s v u (gradField ψ) := fun u => rfl
  simp only [hedge]
  ring
end

end AVRegularity.CycleComparison.Coarse
end
