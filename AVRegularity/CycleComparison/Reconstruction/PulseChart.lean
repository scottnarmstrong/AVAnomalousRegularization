-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.TailConstructed.RawFluxOrderZero
public import AVRegularity.CycleComparison.Lift.LiftSourceBlockCoefficientAction
import AVRegularity.CycleComparison.Lift.SettingLiftPolyTimeIntegral
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
public import AVRegularity.CycleComparison.Reconstruction.ChainLinear
import AVRegularity.CycleComparison.Residual.TailJets
public import AVRegularity.CycleComparison.Reconstruction.InvPiola
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Lift.SettingLiftSourceBlockCoefficient

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Depth truncation of the lifted means** (the lift of grade `q` applied to the mean of grade
`r` is a composite of `q + r` source edges, and the source graph has depth at most `H`,
`IsLiftSetting.depth`).

The source graph has an edge `u → v` when some constituent list `edge v u d` is nonempty
(`IsEdge`). `deepSet edge m` is the set of components at the end of an edge path of length `m`.
It is empty for `m = H + 1` (`notMem_deepSet_of_depth`).

* **Coefficients.** The coefficient bounds of `setting_tailRaw_coefficient_data` carry the
  envelope power `F^q`, `F = physicalEdgeEnvelopeMatrix π b`. The setting's envelope `b` only
  majorizes the constituent jets, so `F` need not be nilpotent. Restricting `b` to the edges
  (`edgeRestrict`) keeps the setting (`setting_edgeRestrict`) and makes `F^q_{vu} ≠ 0` force an
  edge path of length `q` from `u` to `v` (`reach_of_finiteMatrixPower_ne_zero`). In particular
  `F^q = 0` for `q > H`. Hence `Cc q` maps fields
  supported on `deepSet m` to fields supported on `deepSet (m + q)` (`setting_liftApply_vanish`).
* **Means.** The cell operators act componentwise, and the source operator moves support one edge
  forward. So `liftMean r` maps `deepSet m` to `deepSet (m + r)` (`setting_liftMean_vanish`).
  No smoothness is used: a component that vanishes identically has vanishing `fderiv` component,
  whether or not the field is differentiable (`fderiv_apply_eq_zero`).
* **Truncation.** `liftPolyField Cc N ε q (liftMeanPoly … r) = 0` for `q, r ≤ H < q + r` on the
  window (`setting_liftPolyField_liftMeanPoly_eq_zero`). The grade sum of the mean terms is
  therefore the full product sum (`setting_meanPart_grade_sum`). -/

section Combinatorics

/-- Summing over the antidiagonals of the grades `≤ H` is summing over all pairs of grades `≤ H`,
when the pairs of total grade above `H` contribute nothing. -/
theorem sum_antidiagonal_eq_sum_range_range {M : Type*} [AddCommMonoid M] (H : ℕ)
    (T : ℕ → ℕ → M) (hT : ∀ q r, q ≤ H → r ≤ H → H < q + r → T q r = 0) :
    ∑ hh ∈ Finset.range (H + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, T p.1 p.2 =
      ∑ q ∈ Finset.range (H + 1), ∑ r ∈ Finset.range (H + 1), T q r := by
  have h1 : ∀ hh, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh, T p.1 p.2 =
      ∑ k ∈ Finset.range (hh + 1), T k (hh - k) :=
    fun hh => Finset.Nat.sum_antidiagonal_eq_sum_range_succ T hh
  rw [Finset.sum_congr rfl fun hh _ => h1 hh, Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqH : q ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
  rw [← Finset.sum_range_add_sum_Ico _ (show H + 1 - q ≤ H + 1 by omega)]
  have hz : ∑ r ∈ Finset.Ico (H + 1 - q) (H + 1), T q r = 0 :=
    Finset.sum_eq_zero fun r hr => by
      have hr' := Finset.mem_Ico.1 hr
      exact hT q r hqH (by omega) (by omega)
  rw [hz, add_zero]

end Combinatorics

section Graph

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ}

/-- `u → v` is an edge of the source graph: some constituent list from `u` into `v` is nonempty. -/
def IsEdge (edge : ConstituentEdges D h) (u v : ι) : Prop := ∃ d, edge v u d ≠ []

/-- The components at the end of an edge path of length `m`. -/
def deepSet (edge : ConstituentEdges D h) : ℕ → Set ι
  | 0 => Set.univ
  | m + 1 => {v | ∃ w ∈ deepSet edge m, IsEdge edge w v}

open Classical in
/-- The envelope matrix restricted to the edges of the source graph. -/
def edgeRestrict (edge : ConstituentEdges D h) (b : ι → ι → ℝ) : ι → ι → ℝ :=
  fun v u => if IsEdge edge u v then b v u else 0

theorem edgeRestrict_of_isEdge {edge : ConstituentEdges D h} {b : ι → ι → ℝ} {v u : ι}
    (hE : IsEdge edge u v) : edgeRestrict edge b v u = b v u :=
  ite_eq_left hE

theorem edgeRestrict_of_not_isEdge {edge : ConstituentEdges D h} {b : ι → ι → ℝ} {v u : ι}
    (hE : ¬IsEdge edge u v) : edgeRestrict edge b v u = 0 :=
  ite_eq_right hE

/-- A member of `deepSet edge m` ends an edge path of length `m`. -/
theorem exists_path_of_mem_deepSet (edge : ConstituentEdges D h) (m : ℕ) :
    ∀ v, v ∈ deepSet edge m → ∃ p : Fin (m + 1) → ι, p (Fin.last m) = v ∧
      ∀ k : Fin m, IsEdge edge (p k.castSucc) (p k.succ) := by
  induction m with
  | zero => intro v _; exact ⟨fun _ => v, rfl, fun k => k.elim0⟩
  | succ m ih =>
    intro v hv
    obtain ⟨w, hw, hwv⟩ := hv
    obtain ⟨p, hp, hpe⟩ := ih w hw
    refine ⟨Fin.snoc (α := fun _ => ι) p v, Fin.snoc_last _ _, fun k => ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_) k
    · show IsEdge edge (Fin.snoc (α := fun _ => ι) p v (Fin.castSucc (Fin.last m)))
        (Fin.snoc (α := fun _ => ι) p v (Fin.last (m + 1)))
      rw [Fin.snoc_castSucc, Fin.snoc_last, hp]
      exact hwv
    · show IsEdge edge (Fin.snoc (α := fun _ => ι) p v (Fin.castSucc (Fin.castSucc i)))
        (Fin.snoc (α := fun _ => ι) p v (Fin.castSucc (Fin.succ i)))
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact hpe i

/-- **No edge path of length `H + 1`**: `deepSet edge (H + 1)` is empty for a graph of depth at
most `H`. -/
theorem notMem_deepSet_of_depth {edge : ConstituentEdges D h} {H : ℕ}
    (hd : HasDepthAtMost edge H) (v : ι) : v ∉ deepSet edge (H + 1) := by
  intro hv
  obtain ⟨p, -, hpe⟩ := exists_path_of_mem_deepSet edge (H + 1) v hv
  obtain ⟨k, hk⟩ := hd p
  obtain ⟨d, hne⟩ := hpe k
  exact hne (hk d)

theorem deepSet_succ_subset (edge : ConstituentEdges D h) (m : ℕ) :
    deepSet edge (m + 1) ⊆ deepSet edge m := by
  induction m with
  | zero => intro v _; exact Set.mem_univ v
  | succ m ih =>
    rintro v ⟨w, hw, hwv⟩
    exact ⟨w, ih hw, hwv⟩

theorem deepSet_antitone (edge : ConstituentEdges D h) {m n : ℕ} (hmn : m ≤ n) :
    deepSet edge n ⊆ deepSet edge m := by
  induction hmn with
  | refl => exact subset_rfl
  | step _ ih => exact (deepSet_succ_subset edge _).trans ih

/-- The edge-restricted envelope is still an envelope: off the edges the constituent jets vanish. -/
theorem isScaledJetEnvelope_edgeRestrict [Fintype ι] {π : ι → ℝ} {edge : ConstituentEdges D h}
    {I : Set ℝ} {lam : ℝ} {Cj : ℕ → ℕ → ℝ} {Ks Ls : ℕ} {b : ι → ι → ℝ} {Θ : ℝ}
    (hb : IsScaledJetEnvelope π edge I lam Cj Ks Ls b Θ) :
    IsScaledJetEnvelope π edge I lam Cj Ks Ls (edgeRestrict edge b) Θ := by
  have hle : ∀ v u, edgeRestrict edge b v u ≤ b v u := by
    intro v u
    by_cases hE : IsEdge edge u v
    · exact (edgeRestrict_of_isEdge hE).le
    · exact (edgeRestrict_of_not_isEdge hE).le.trans (hb.nonneg v u)
  refine ⟨fun v u => ?_, fun v => (Finset.sum_le_sum fun u _ => hle v u).trans (hb.row_sum v),
    fun u => (Finset.sum_le_sum fun v _ => hle v u).trans (hb.col_sum u),
    fun v u r hr q hq => ?_⟩
  · by_cases hE : IsEdge edge u v
    · rw [edgeRestrict_of_isEdge hE]
      exact hb.nonneg v u
    · exact (edgeRestrict_of_not_isEdge hE).symm.le
  · by_cases hE : IsEdge edge u v
    · rw [edgeRestrict_of_isEdge hE]
      exact hb.jets v u r hr q hq
    · have hnil : ∀ d, edge v u d = [] := fun d => by
        by_contra hd
        exact hE ⟨d, hd⟩
      simp [hnil]

/-- **The setting with the edge-restricted envelope.** -/
theorem setting_edgeRestrict [Fintype ι] {H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D}
    {π : ι → ℝ} {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {b : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ) :
    IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj
      (edgeRestrict Q.edge b) Θ :=
  { P with envelope := isScaledJetEnvelope_edgeRestrict P.envelope }

/-- A nonzero entry of the physical edge-restricted envelope is an edge. -/
theorem isEdge_of_physical_ne_zero {π : ι → ℝ} {b : ι → ι → ℝ} {edge : ConstituentEdges D h}
    {v w : ι} (hne : Lift.physicalEdgeEnvelopeMatrix π (edgeRestrict edge b) v w ≠ 0) :
    IsEdge edge w v := by
  by_contra hE
  apply hne
  show edgeRestrict edge b v w / Real.sqrt (π w / π v) = 0
  rw [edgeRestrict_of_not_isEdge hE, zero_div]

/-- **Reachability from the envelope powers.** A nonzero entry `(v, u)` of the `q`-th power of the
physical edge-restricted envelope moves `deepSet m` into `deepSet (m + q)`. -/
theorem reach_of_finiteMatrixPower_ne_zero [Fintype ι] [DecidableEq ι] (π : ι → ℝ)
    (b : ι → ι → ℝ) (edge : ConstituentEdges D h) (q : ℕ) :
    ∀ v u, Lift.finiteMatrixPower (Lift.physicalEdgeEnvelopeMatrix π (edgeRestrict edge b)) q v u
      ≠ 0 → ∀ j, u ∈ deepSet edge j → v ∈ deepSet edge (j + q) := by
  induction q with
  | zero =>
    intro v u hvu j hu
    by_cases hv : v = u
    · subst hv
      exact hu
    · exfalso
      apply hvu
      rw [Lift.finiteMatrixPower_zero]
      exact ite_eq_right hv
  | succ q ih =>
    intro v u hvu j hu
    rw [Lift.finiteMatrixPower_succ] at hvu
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hvu
    rw [← Nat.add_assoc]
    exact ⟨w, ih w u (right_ne_zero_of_mul hw) j hu,
      isEdge_of_physical_ne_zero (left_ne_zero_of_mul hw)⟩

end Graph

section Components

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

omit [Fintype ι] in
/-- A component that vanishes identically has vanishing derivative component (with or without
differentiability). -/
theorem fderiv_apply_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ∀ i, h i} {v : ι} (hf : ∀ x, f x v = 0) (x y : E) : fderiv ℝ f x y v = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · have h1 := hasFDerivAt_pi'.1 hd.hasFDerivAt v
    have h0 : (fun x' => f x' v) = fun _ => (0 : h v) := funext hf
    rw [h0] at h1
    have h2 := h1.unique (hasFDerivAt_const (0 : h v) x)
    simpa using DFunLike.congr_fun h2 y
  · simp [fderiv_zero_of_not_differentiableAt hd]

theorem slowPartial_apply_eq_zero {Φ : Vec 2 → Vec 2 → ∀ i, h i} {v : ι}
    (hΦ : ∀ X z, Φ X z v = 0) (i : Fin 2) (X z : Vec 2) : slowPartial i Φ X z v = 0 :=
  fderiv_apply_eq_zero (fun X' => hΦ X' z) X (basisVec i)

theorem fastPartial_apply_eq_zero {Φ : Vec 2 → Vec 2 → ∀ i, h i} {v : ι}
    (hΦ : ∀ X z, Φ X z v = 0) (i : Fin 2) (X z : Vec 2) : fastPartial i Φ X z v = 0 :=
  fderiv_apply_eq_zero (fun z' => hΦ X z') z (basisVec i)

theorem orderedDerivative_apply_eq_zero {f : Vec 2 → ∀ i, h i} {v : ι} (hf : ∀ X, f X v = 0)
    {m : ℕ} (α : DerivativeWord2 m) (X : Vec 2) : orderedDerivative α f X v = 0 := by
  have key : ∀ (l : List (Fin 2)) (g : Vec 2 → ∀ i, h i), (∀ X, g X v = 0) →
      ∀ X, (l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) g) X v = 0 := by
    intro l
    induction l with
    | nil => intro g hg; exact hg
    | cons i l ih => intro g hg; exact ih _ fun x => fderiv_apply_eq_zero hg x (basisVec i)
  exact key (List.ofFn α) f hf X

theorem dEps_apply_eq_zero {η ε : ℝ} {Ψ : Vec 2 → Vec 2 → ∀ i, h i} {v : ι}
    (hΨ : ∀ X z, Ψ X z v = 0) (i : Fin 2) (X z : Vec 2) : dEps η ε i Ψ X z v = 0 := by
  show (fastPartial i Ψ X z + (Real.sqrt η * ε) • slowPartial i Ψ X z) v = 0
  rw [Pi.add_apply, Pi.smul_apply, fastPartial_apply_eq_zero hΨ, slowPartial_apply_eq_zero hΨ,
    smul_zero, add_zero]

theorem dEpsWord_apply_eq_zero {η ε : ℝ} {Ψ : Vec 2 → Vec 2 → ∀ i, h i} {v : ι}
    (hΨ : ∀ X z, Ψ X z v = 0) {m : ℕ} (α : DerivativeWord2 m) (X z : Vec 2) :
    dEpsWord η ε α Ψ X z v = 0 := by
  have key : ∀ (l : List (Fin 2)) (Ψ' : Vec 2 → Vec 2 → ∀ i, h i), (∀ X z, Ψ' X z v = 0) →
      ∀ X z, (l.foldl (fun Ψ'' i => dEps η ε i Ψ'') Ψ') X z v = 0 := by
    intro l
    induction l with
    | nil => intro Ψ' hΨ'; exact hΨ'
    | cons i l ih => intro Ψ' hΨ'; exact ih _ fun X z => dEps_apply_eq_zero hΨ' i X z
  exact key (List.ofFn α) Ψ hΨ X z

theorem iteratedDeriv_apply_eq_zero {f : ℝ → ∀ i, h i} {v : ι} (hf : ∀ x, f x v = 0) (j : ℕ)
    (x : ℝ) : iteratedDeriv j f x v = 0 := by
  induction j generalizing x with
  | zero => rw [iteratedDeriv_zero]; exact hf x
  | succ j ih => rw [iteratedDeriv_succ]; exact fderiv_apply_eq_zero ih x 1

/-- The `v` component of a lift action vanishes when every input component `u` either meets a
vanishing coefficient `(v, u)` or vanishes identically. -/
theorem liftApply_apply_eq_zero {M : ℕ} {c : LiftCoeff ι h} {a : ℝ → Vec 2 → ∀ i, h i}
    {t : ℝ} {X z : Vec 2} {v : ι}
    (hc : ∀ m (α : DerivativeWord2 m) u, c m α t X z v u = 0 ∨ ∀ X', a t X' u = 0) :
    liftApply M c a t X z v = 0 := by
  show ∑ m ∈ Finset.range (M + 1), ∑ α : DerivativeWord2 m, ∑ u : ι,
    c m α t X z v u (orderedDerivative α (a t) X u) = 0
  refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun α _ =>
    Finset.sum_eq_zero fun u _ => ?_
  rcases hc m α u with h0 | h0
  · simp [h0]
  · rw [orderedDerivative_apply_eq_zero h0 α X, map_zero]

theorem cellB1_apply_eq_zero {η : ℝ} {G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ}
    {W : ℝ → Vec 2 → Vec 2} {t : ℝ} {Φ : Vec 2 → Vec 2 → ∀ i, h i} {v : ι}
    (hΦ : ∀ X z, Φ X z v = 0) (X z : Vec 2) : cellB1 η G W t Φ X z v = 0 := by
  have hs : ∀ k X z, slowPartial k Φ X z v = 0 := fun k X z => slowPartial_apply_eq_zero hΦ k X z
  have hfs : ∀ i j X z, fastPartial i (slowPartial j Φ) X z v = 0 :=
    fun i j X z => fastPartial_apply_eq_zero (hs j) i X z
  have hsf : ∀ i j X z,
      slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') X z v = 0 := by
    intro i j X z
    refine slowPartial_apply_eq_zero (fun X' z' => ?_) i X z
    show (G t X' i j • fastPartial j Φ X' z') v = 0
    rw [Pi.smul_apply, fastPartial_apply_eq_zero hΦ j X' z', smul_zero]
  simp [cellB1, hs, hfs, hsf]

theorem cellB2_apply_eq_zero {η : ℝ} {G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ} {t : ℝ}
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {v : ι} (hΦ : ∀ X z, Φ X z v = 0) (X z : Vec 2) :
    cellB2 η G t Φ X z v = 0 := by
  have hsf : ∀ i j X z,
      slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z') X z v = 0 := by
    intro i j X z
    refine slowPartial_apply_eq_zero (fun X' z' => ?_) i X z
    show (G t X' i j • slowPartial j Φ X' z') v = 0
    rw [Pi.smul_apply, slowPartial_apply_eq_zero hΦ j X' z', smul_zero]
  simp [cellB2, hsf]

/-- The `v` component of the source flux vanishes when every input component `u` either has no
edge into `v` or vanishes identically. -/
theorem sourceFlux_apply_eq_zero {D : ℕ} {edge : ConstituentEdges D h} {η ε t : ℝ}
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {v : ι}
    (hv : ∀ u, (∀ d, edge v u d = []) ∨ ∀ X z, Φ X z u = 0) (k : Fin 2) (X z : Vec 2) :
    sourceFlux edge η ε t Φ k X z v = 0 := by
  show ∑ u : ι, ∑ d : Finset.Icc 2 D, ((edge v u d).map fun γ =>
    ∑ α : DerivativeWord2 (d.1 - 1), (γ.coeff α t X z k) • γ.map (dEpsWord η ε α Φ X z u)).sum = 0
  refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun d _ => ?_
  rcases hv u with he | hz
  · rw [he d, List.map_nil, List.sum_nil]
  · refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hx
    show ∑ α : DerivativeWord2 (d.1 - 1), (γ.coeff α t X z k) • γ.map (dEpsWord η ε α Φ X z u) = 0
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [dEpsWord_apply_eq_zero hz α X z, map_zero, smul_zero]

theorem sourceOp_apply_eq_zero {D : ℕ} {edge : ConstituentEdges D h} {η t : ℝ}
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {v : ι}
    (hv : ∀ u, (∀ d, edge v u d = []) ∨ ∀ X z, Φ X z u = 0) (ε : ℝ) (X z : Vec 2) :
    sourceOp edge η ε t Φ X z v = 0 := by
  show (∑ k : Fin 2, dEps η ε k (sourceFlux edge η ε t Φ k) X z) v = 0
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun k _ =>
    dEps_apply_eq_zero (fun X' z' => sourceFlux_apply_eq_zero hv k X' z') k X z

theorem sourceCoeff_apply_eq_zero {D : ℕ} {edge : ConstituentEdges D h} {η t : ℝ}
    {Φ : Vec 2 → Vec 2 → ∀ i, h i} {v : ι}
    (hv : ∀ u, (∀ d, edge v u d = []) ∨ ∀ X z, Φ X z u = 0) (j : ℕ) (X z : Vec 2) :
    sourceCoeff edge η j t Φ X z v = 0 := by
  show (((j.factorial : ℝ)⁻¹) • iteratedDeriv j (fun ε : ℝ => sourceOp edge η ε t Φ X z) 0) v = 0
  rw [Pi.smul_apply, iteratedDeriv_apply_eq_zero (fun ε => sourceOp_apply_eq_zero hv ε X z) j 0,
    smul_zero]

/-- The `v` component of the uncentered cell source `A_n^{(hh)}` vanishes when the lifts entering it
vanish in the components that reach `v`. -/
theorem liftA_apply_eq_zero {D : ℕ} {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h}
    {a : ℝ → Vec 2 → ∀ i, h i} {hh n : ℕ} {t : ℝ} {v : ι}
    (h1 : ∀ X z, liftApply (n - 1) (Cc hh (n - 1)) a t X z v = 0)
    (h2 : ∀ X z, liftApply (n - 2) (Cc hh (n - 2)) a t X z v = 0)
    (h3 : hh ≠ 0 → ∀ j u, (∀ d, Q.edge v u d = []) ∨
      ∀ X z, liftApply (n - j) (Cc (hh - 1) (n - j)) a t X z u = 0) (X z : Vec 2) :
    liftA Q Cc a hh n t X z v = 0 := by
  show (cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1)) a t) X z
      + (if 2 ≤ n then cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) a t) X z else 0)
      - (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
          sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) a t) X z)) v = 0
  have e2 : (if 2 ≤ n then cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) a t) X z
      else 0) v = 0 := by
    by_cases hn : 2 ≤ n
    · rw [ite_eq_left hn]
      exact cellB2_apply_eq_zero h2 X z
    · rw [ite_eq_right hn, Pi.zero_apply]
  have e3 : (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) a t) X z) v = 0 := by
    by_cases hh0 : hh = 0
    · rw [ite_eq_left hh0, Pi.zero_apply]
    · rw [ite_eq_right hh0, Finset.sum_apply]
      exact Finset.sum_eq_zero fun j _ => sourceCoeff_apply_eq_zero (h3 hh0 j) j X z
  rw [Pi.sub_apply, Pi.add_apply, cellB1_apply_eq_zero h1 X z, e2, e3, add_zero, sub_zero]

/-- The `v` component of a Bochner integral of a field with vanishing `v` component vanishes. -/
theorem integral_apply_eq_zero [∀ i, CompleteSpace (h i)] {β : Type*} [MeasurableSpace β]
    {μ : Measure β} {F : β → ∀ i, h i} {v : ι} (hF : ∀ z, F z v = 0) :
    (∫ z, F z ∂μ) v = 0 := by
  by_cases hi : Integrable F μ
  · have e := (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).integral_comp_comm hi
    simp only [ContinuousLinearMap.proj_apply] at e
    rw [← e]
    simp [hF]
  · simp [integral_undef hi]

/-- **The truncated lift is additive in the coarse field** over finitely many inputs, each
`C^N` at the time used. -/
theorem liftPolyField_sum_input (Cc : ℕ → ℕ → LiftCoeff ι h) (N : ℕ) (ε : ℝ) (q : ℕ)
    (S : Finset ℕ) (A : ℕ → ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (hA : ∀ r ∈ S, ContDiff ℝ (N : ℕ∞) (A r t)) (X z : Vec 2) :
    liftPolyField Cc N ε q (fun s' X' => ∑ r ∈ S, A r s' X') t X z =
      ∑ r ∈ S, liftPolyField Cc N ε q (A r) t X z := by
  have hn : ∀ n ∈ Finset.range (N + 1),
      liftApply n (Cc q n) (fun s' X' => ∑ r ∈ S, A r s' X') t X z =
        ∑ r ∈ S, liftApply n (Cc q n) (A r) t X z := by
    intro n hn
    have hnN : n ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    have h1 := Lift.liftApply_input_finset_synthesis S n (Cc q n) (fun _ => (1 : ℝ))
      (fun r => A r t) (fun r hr => (hA r hr).of_le (by exact_mod_cast hnN)) t X z
    simp only [one_smul] at h1
    exact h1
  show ∑ n ∈ Finset.range (N + 1), ε ^ n •
      liftApply n (Cc q n) (fun s' X' => ∑ r ∈ S, A r s' X') t X z =
    ∑ r ∈ S, ∑ n ∈ Finset.range (N + 1), ε ^ n • liftApply n (Cc q n) (A r) t X z
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn' => ?_
  rw [hn n hn', Finset.smul_sum]

end Components

section Setting

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {b : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)

include P in
/-- **Lift coefficients follow edge paths.** On the window, a coefficient `(v, u)` of grade `q`
vanishes unless `v` is reached from `u` by edge paths of length `q`. -/
theorem setting_coeff_eq_zero_of_not_reach {sX sZ : ℕ} (hsZ : 1 ≤ sZ)
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {q : ℕ}
    (hq : q ≤ H) (d m : ℕ) (α : DerivativeWord2 m) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁)
    (X z : Vec 2) {v u : ι} (hvu : ¬∀ j, u ∈ deepSet Q.edge j → v ∈ deepSet Q.edge (j + q)) :
    Cc q d m α t X z v u = 0 := by
  classical
  let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
  have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
  by_cases hmd : m ≤ d
  · have data := TailConstructed.setting_tailRaw_coefficient_data (setting_edgeRestrict P)
      sX sZ hsZ Cc hseq 0 0 (Nat.zero_le _) (Nat.zero_le _) q hq d
    have hF : Lift.finiteMatrixPower (Lift.physicalEdgeEnvelopeMatrix π (edgeRestrict Q.edge b))
        q v u = 0 := by
      by_contra hne
      exact hvu (reach_of_finiteMatrixPower_ne_zero π b Q.edge q v u hne)
    have hb := data.bound m hmd α v u 0 le_rfl 0 le_rfl t ht X z
    simp only [hF, mul_zero, zero_mul, norm_iteratedFDeriv_zero] at hb
    exact norm_le_zero_iff.1 hb
  · exact hseq.2.2.2.1 q hq d m (by omega) α t X z v u

include P in
/-- **The lift of grade `q` moves support `q` edges forward.** If the coarse field vanishes at
time `t` outside `deepSet m`, its lift of grade `q` vanishes outside `deepSet (m + q)`. -/
theorem setting_liftApply_vanish {sX sZ : ℕ} (hsZ : 1 ≤ sZ) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {q : ℕ} (hq : q ≤ H) (d : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc t₀ t₁) (A : ℝ → Vec 2 → ∀ i, h i) {m : ℕ}
    (hA : ∀ u, u ∉ deepSet Q.edge m → ∀ X, A t X u = 0) :
    ∀ v, v ∉ deepSet Q.edge (m + q) → ∀ X z, liftApply d (Cc q d) A t X z v = 0 := by
  intro v hv X z
  refine liftApply_apply_eq_zero fun m' α u => ?_
  by_cases hu : u ∈ deepSet Q.edge m
  · left
    exact setting_coeff_eq_zero_of_not_reach P hsZ hseq hq d m' α ht X z fun hr => hv (hr m hu)
  · right
    exact hA u hu

include P in
/-- **The mean of grade `r` moves support `r` edges forward.** -/
theorem setting_liftMean_vanish {sX sZ : ℕ} (hsZ : 1 ≤ sZ) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {r : ℕ} (hr : r ≤ H) (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Icc t₀ t₁) (A : ℝ → Vec 2 → ∀ i, h i) {m : ℕ}
    (hA : ∀ u, u ∉ deepSet Q.edge m → ∀ X, A t X u = 0) :
    ∀ v, v ∉ deepSet Q.edge (m + r) → ∀ X, liftMean Q Cc A r n t X v = 0 := by
  have : ∀ i, CompleteSpace (h i) := fun i => FiniteDimensional.complete ℝ (h i)
  intro v hv X
  have hC : ∀ j X' z', liftApply j (Cc r j) A t X' z' v = 0 := fun j X' z' =>
    setting_liftApply_vanish P hsZ hseq hr j ht A hA v hv X' z'
  have hsrc : r ≠ 0 → ∀ j u, (∀ d, Q.edge v u d = []) ∨
      ∀ X' z', liftApply (n - j) (Cc (r - 1) (n - j)) A t X' z' u = 0 := by
    intro hr0 j u
    by_cases hE : IsEdge Q.edge u v
    · right
      intro X' z'
      refine setting_liftApply_vanish P hsZ hseq (q := r - 1) (by omega) (n - j) ht A hA u ?_
        X' z'
      intro hu
      apply hv
      have hm : m + r = m + (r - 1) + 1 := by omega
      rw [hm]
      exact ⟨u, hu, hE⟩
    · left
      intro d
      by_contra hd
      exact hE ⟨d, hd⟩
  show (∫ z in AVenhance.unitCube, liftA Q Cc A r n t X z) v = 0
  exact integral_apply_eq_zero fun z => liftA_apply_eq_zero (hC (n - 1)) (hC (n - 2)) hsrc X z

include P in
/-- **The mean polynomial of grade `r` moves support `r` edges forward.** -/
theorem setting_liftMeanPoly_vanish {sX sZ : ℕ} (hsZ : 1 ≤ sZ) {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (ε : ℝ) {r : ℕ} (hr : r ≤ H) {t : ℝ}
    (ht : t ∈ Set.Icc t₀ t₁) (A : ℝ → Vec 2 → ∀ i, h i) {m : ℕ}
    (hA : ∀ u, u ∉ deepSet Q.edge m → ∀ X, A t X u = 0) :
    ∀ v, v ∉ deepSet Q.edge (m + r) → ∀ X, liftMeanPoly Q Cc N ε A r t X v = 0 := by
  intro v hv X
  show (∑ n ∈ Finset.Icc 2 (N + D), ε ^ n • liftMean Q Cc A r n t X) v = 0
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [Pi.smul_apply, setting_liftMean_vanish P hsZ hseq hr n ht A hA v hv X, smul_zero]

include P in
/-- **Depth truncation.** On the window, the lift of grade `q` of the mean polynomial of grade `r`
vanishes when `H < q + r`, for every coarse field (no smoothness is needed). -/
theorem setting_liftPolyField_liftMeanPoly_eq_zero {sX sZ : ℕ} (hsZ : 1 ≤ sZ)
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (ε : ℝ)
    (g : ℝ → Vec 2 → ∀ i, h i) {q r : ℕ} (hq : q ≤ H) (hr : r ≤ H) (hqr : H < q + r) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) (X z : Vec 2) :
    liftPolyField Cc N ε q (liftMeanPoly Q Cc N ε g r) s X z = 0 := by
  have hB : ∀ v, v ∉ deepSet Q.edge (0 + r) → ∀ X', liftMeanPoly Q Cc N ε g r s X' v = 0 :=
    setting_liftMeanPoly_vanish P hsZ hseq ε hr hs g (m := 0)
      fun u hu => absurd (Set.mem_univ u) hu
  have hout : ∀ v, v ∉ deepSet Q.edge (0 + r + q) := fun v hv =>
    notMem_deepSet_of_depth P.depth v (deepSet_antitone Q.edge (by omega) hv)
  funext v
  show (∑ n ∈ Finset.range (N + 1), ε ^ n •
    liftApply n (Cc q n) (liftMeanPoly Q Cc N ε g r) s X z) v = 0
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [Pi.smul_apply, setting_liftApply_vanish P hsZ hseq hq n hs (liftMeanPoly Q Cc N ε g r) hB v
    (hout v) X z, smul_zero]

include P in
/-- The mean polynomial of a smooth time-independent coarse field is `C^N` in the slow variable on
the window. -/
theorem setting_liftMeanPoly_contDiff {sX sZ : ℕ} (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (ε : ℝ)
    {r : ℕ} (hr : r ≤ H) (g : Vec 2 → ∀ i, h i) (hg : ContDiff ℝ (⊤ : ℕ∞) g) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) :
    ContDiff ℝ (N : ℕ∞) (liftMeanPoly Q Cc N ε (fun _ => g) r s) := by
  classical
  let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
  have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
  have hreserve : N + (N + D) ≤ qs := by
    have := Lift.setting_tail_ambient_supported P
    omega
  show ContDiff ℝ (N : ℕ∞)
    (fun X => ∑ n ∈ Finset.Icc 2 (N + D), ε ^ n • liftMean Q Cc (fun _ => g) r n s X)
  exact ContDiff.sum fun n hn => (Lift.setting_mean_action_contDiff_upto P sX sZ hsX hsZ Cc
    hseq N hreserve r hr n (Finset.mem_Icc.1 hn).1 (Finset.mem_Icc.1 hn).2 g hg s hs).const_smul _

include P in
/-- **The grade sum of the mean terms is the full product sum.** On the window, for a smooth
time-independent coarse field `g`, summing the mean terms of the lift identity over the grades
`hh ≤ H` gives the lift of each grade `q ≤ H` applied to the sum of all means of grades `≤ H`. -/
theorem setting_meanPart_grade_sum {sX sZ : ℕ} (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (ε : ℝ)
    (g : Vec 2 → ∀ i, h i) (hg : ContDiff ℝ (⊤ : ℕ∞) g) {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁)
    (X z : Vec 2) :
    ∑ hh ∈ Finset.range (H + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftPolyField Cc N ε p.1 (liftMeanPoly Q Cc N ε (fun _ => g) p.2) s X z =
      ∑ q ∈ Finset.range (H + 1), liftPolyField Cc N ε q
        (fun s' X' => ∑ r ∈ Finset.range (H + 1), liftMeanPoly Q Cc N ε (fun _ => g) r s' X')
          s X z := by
  rw [sum_antidiagonal_eq_sum_range_range H
    (fun q r => liftPolyField Cc N ε q (liftMeanPoly Q Cc N ε (fun _ => g) r) s X z)
    (fun q r hq hr hqr => setting_liftPolyField_liftMeanPoly_eq_zero P (by omega) hseq ε _
      hq hr hqr hs X z)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [liftPolyField_sum_input Cc N ε q (Finset.range (H + 1))
    (liftMeanPoly Q Cc N ε (fun _ => g)) s
    (fun r hr => setting_liftMeanPoly_contDiff P hsX hsZ hseq ε
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)) g hg hs) X z]

end Setting

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The lift identity for a time-dependent coarse field** (the identity of `cycle_lift_identity`
with a coarse field that depends on time). The lift coefficients have the input-free time primitive
of the lift recursion (`setting_lift_coefficient_source_time_integral`). If the coarse field `f(s)`
is smooth at every time of the lift window and its jets are of integral type in time with the jets
of `df` as densities, the product rule (`IsPrimOn.clm_apply`) gives the time primitive of the
truncated lift with the frozen-time right side of `cycle_lift_identity` plus the lift of `df`. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- The density of one lift coefficient applied to a vector: linear on the lift window. -/
theorem coefficient_density_linear (sX sZ : ℕ) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh n : ℕ) (hhh : hh ≤ H) (hnN : n ≤ N)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u v : ι) (X z : Vec 2) (s : ℝ)
    (hs : s ∈ Icc a b) :
    IsLinearMap ℝ (fun ξ : h u =>
      -cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n m α s X y v u ξ) z +
        leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n s w)
          m α s X z v u ξ) := by
  have hbox := setting_lift_cross_coefficient_box P sX sZ (by omega) Cc hseq hh hhh n hnN m hm
    α v u s hs
  have hc2 : ∀ ξ : h u, ContDiff ℝ 2 (fun y => Cc hh n m α s X y v u ξ) := fun ξ =>
    ((hbox.1 X).clm_apply contDiff_const).of_le (by norm_num)
  have hsyn : ∀ (c : ℝ) (ξ η : h u),
      cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n m α s X y v u (c • ξ + η)) z =
        c • cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n m α s X y v u ξ) z +
          cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n m α s X y v u η) z := by
    intro c ξ η
    have h2 := cellOperator_finite_synthesis (Q.G s X) (Q.v s) ![c, 1]
      ![fun y => Cc hh n m α s X y v u ξ, fun y => Cc hh n m α s X y v u η]
      (fun j => by fin_cases j <;> simp [hc2]) z
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul] at h2
    rw [← h2]
    congr 1
    funext y
    rw [map_add, map_smul]
  have h0 : cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n m α s X y v u (0 : h u)) z = 0 := by
    have he : (fun y => Cc hh n m α s X y v u (0 : h u)) = fun _ => (0 : h v) :=
      funext fun _ => map_zero _
    rw [he]
    simp [cellOperator]
  refine ⟨fun ξ η => ?_, fun c ξ => ?_⟩
  · have h1 := hsyn 1 ξ η
    simp only [one_smul] at h1
    rw [h1, map_add, neg_add]
    abel
  · have h1 := hsyn c ξ 0
    simp only [add_zero] at h1
    rw [h1, h0, add_zero, map_smul, smul_add, smul_neg]

include P in
/-- **Per-degree time primitive of the lift of a time-dependent coarse field.** On the lift
window, `s ↦ (C_n f)(s, X, z)` has density `-𝒫₀ (C_n f(s)) + (cell source of f(s)) + C_n ḟ(s)`. -/
theorem setting_liftApply_prim_td (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (f df : ℝ → Vec 2 → ∀ i, h i) (hf : ∀ s ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (f s))
    (hjet : ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m) (X : Vec 2) (u : ι),
      IsPrimOn a b (fun s => orderedDerivative α (f s) X u)
        (fun s => orderedDerivative α (df s) X u))
    (X z : Vec 2) (v : ι) :
    IsPrimOn a b (fun s => liftApply n (Cc hh n) f s X z v)
      (fun s => -cellOperator (Q.G s X) (Q.v s)
          (fun y => liftApply n (Cc hh n) (fun _ => f s) s X y v) z +
        liftCellSource Q Cc (fun _ => f s) hh n s X z v + liftApply n (Cc hh n) df s X z v) := by
  classical
  have hab : a ≤ b := P.window
  have hr : 0 + (N + D) ≤ qs := by
    have := setting_ambient_output_supported P
    omega
  have hp : ∀ p ∈ (Finset.univ : Finset (LiftActionIndex ι n)), IsPrimOn a b
      (fun s => Cc hh n p.1.val p.2.1 s X z v p.2.2 (orderedDerivative p.2.1 (f s) X p.2.2))
      (fun s => (-cellOperator (Q.G s X) (Q.v s)
          (fun y => Cc hh n p.1.val p.2.1 s X y v p.2.2
            (orderedDerivative p.2.1 (f s) X p.2.2)) z +
          leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n s w)
            p.1.val p.2.1 s X z v p.2.2 (orderedDerivative p.2.1 (f s) X p.2.2)) +
        Cc hh n p.1.val p.2.1 s X z v p.2.2 (orderedDerivative p.2.1 (df s) X p.2.2)) := by
    intro p _
    have hm : p.1.val ≤ n := by have := p.1.isLt; omega
    refine IsPrimOn.clm_apply hab (fun s => Cc hh n p.1.val p.2.1 s X z v p.2.2)
      (fun s ξ => -cellOperator (Q.G s X) (Q.v s) (fun y => Cc hh n p.1.val p.2.1 s X y v p.2.2 ξ) z +
        leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n s w)
          p.1.val p.2.1 s X z v p.2.2 ξ)
      (fun s hs => coefficient_density_linear P sX sZ hsZ Cc hseq hh n hhh hnN p.1.val hm p.2.1
        p.2.2 v X z s hs)
      (fun ξ => ?_) (hjet p.1.val hm p.2.1 X p.2.2)
    have hprim := fun t (ht : t ∈ Icc a b) => setting_lift_coefficient_source_time_integral P
      sX sZ hsX hsZ Cc hseq 0 hh n hr hhh hn hnN p.1.val hm p.2.1 p.2.2 v ξ t ht X z
    refine ⟨(hprim b ⟨hab, le_rfl⟩).1, fun s hs => ?_⟩
    have h0 := (hprim a ⟨le_rfl, hab⟩).2
    rw [intervalIntegral.integral_same] at h0
    beta_reduce
    rw [h0, zero_add]
    exact (hprim s hs).2
  refine (IsPrimOn.sum Finset.univ hp).congr hab (fun s _ => ?_) (fun s hs => ?_)
  · exact liftApply_finite_vector_synthesis n (Cc hh n) (f s) s X z v
  · have hc2 : ∀ p : LiftActionIndex ι n, ContDiff ℝ 2 (fun y => Cc hh n p.1.val p.2.1 s X y v
        p.2.2 (orderedDerivative p.2.1 (f s) X p.2.2)) := by
      intro p
      have hm : p.1.val ≤ n := by have := p.1.isLt; omega
      exact (((setting_lift_cross_coefficient_box P sX sZ (by omega) Cc hseq hh hhh
        n hnN p.1.val hm p.2.1 v p.2.2 s hs).1 X).clm_apply contDiff_const).of_le (by norm_num)
    have hcell := cellOperator_finite_synthesis (Q.G s X) (Q.v s)
      (fun _ : LiftActionIndex ι n => (1 : ℝ))
      (fun p y => Cc hh n p.1.val p.2.1 s X y v p.2.2 (orderedDerivative p.2.1 (f s) X p.2.2))
      hc2 z
    simp only [one_smul] at hcell
    have hfield : (fun y => ∑ p : LiftActionIndex ι n, Cc hh n p.1.val p.2.1 s X y v p.2.2
        (orderedDerivative p.2.1 (f s) X p.2.2)) =
        fun y => liftApply n (Cc hh n) (fun _ => f s) s X y v := by
      funext y
      exact liftApply_finite_vector_synthesis n (Cc hh n) (f s) s X y v
    have hsrc : (∑ p : LiftActionIndex ι n,
        leftTermsBlockCoefficient (fun w => liftCellSourceLeftTerms Q Cc hh n s w)
          p.1.val p.2.1 s X z v p.2.2 (orderedDerivative p.2.1 (f s) X p.2.2)) =
        liftCellSource Q Cc (fun _ => f s) hh n s X z v := by
      rw [liftApply_finite_vector_synthesis]
      exact setting_liftSource_blockCoefficient_apply P sX sZ hsX hsZ Cc hseq hh hhh n hn hnN
        (f s) (hf s hs) s hs X z v
    have hdf : (∑ p : LiftActionIndex ι n,
        Cc hh n p.1.val p.2.1 s X z v p.2.2 (orderedDerivative p.2.1 (df s) X p.2.2)) =
        liftApply n (Cc hh n) df s X z v :=
      liftApply_finite_vector_synthesis n (Cc hh n) (df s) s X z v
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← hcell, hfield,
      hsrc, hdf]

include P in
/-- **Time primitive of the truncated lift of a time-dependent coarse field** (component `v`):
the density is the frozen-time right side `liftPositiveTimeRhs` plus the lift of `ḟ`. -/
theorem setting_liftPoly_prim_td (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (ε : ℝ)
    (f df : ℝ → Vec 2 → ∀ i, h i) (hf : ∀ s ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (f s))
    (hjet : ∀ m, m ≤ N → ∀ (α : DerivativeWord2 m) (X : Vec 2) (u : ι),
      IsPrimOn a b (fun s => orderedDerivative α (f s) X u)
        (fun s => orderedDerivative α (df s) X u))
    (X z : Vec 2) (v : ι) :
    IsPrimOn a b (fun s => liftPolyField Cc N ε hh f s X z v)
      (fun s => liftPositiveTimeRhs Q Cc N ε hh (f s) s X z v +
        liftPolyField Cc N ε hh df s X z v) := by
  classical
  have hab : a ≤ b := P.window
  have hrange : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0mem : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  have hz : ∀ (g : ℝ → Vec 2 → ∀ i, h i), ∀ s ∈ Icc a b,
      liftApply 0 (Cc hh 0) g s X z v = if hh = 0 then g s X v else 0 := by
    intro g s hs
    by_cases hh0 : hh = 0
    · subst hh0
      simp only [↓reduceIte]
      exact congrFun (liftSequence_zero_degree_action Q sX sZ a b N H Cc hseq g s hs X z) v
    · simp only [hh0, ↓reduceIte]
      rw [liftApply_zero_degree (Cc hh 0) (fun i => Fin.elim0 i) g s X z v]
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [hseq.2.1 hh (by omega) hhh 0 (fun i => Fin.elim0 i) s X z v u]
      rfl
  have hb : IsPrimOn a b (fun s => if hh = 0 then f s X v else 0)
      (fun s => if hh = 0 then df s X v else 0) := by
    by_cases hh0 : hh = 0
    · simp only [hh0, ↓reduceIte]
      simpa [orderedDerivative] using hjet 0 (Nat.zero_le _) (fun i => Fin.elim0 i) X v
    · simp only [hh0, ↓reduceIte]
      exact IsPrimOn.zero
  have hzero : IsPrimOn a b (fun s => ε ^ 0 • liftApply 0 (Cc hh 0) f s X z v)
      (fun s => ε ^ 0 • liftApply 0 (Cc hh 0) df s X z v) :=
    (hb.congr hab (fun s hs => (hz f s hs).symm) (fun s hs => (hz df s hs).symm)).const_smul _
  have hpos := IsPrimOn.sum (Finset.Icc 1 N) fun n hn =>
    (setting_liftApply_prim_td P sX sZ hsX hsZ Cc hseq hh n hhh (Finset.mem_Icc.1 hn).1
      (Finset.mem_Icc.1 hn).2 f df hf
      (fun m hm => hjet m (hm.trans (Finset.mem_Icc.1 hn).2)) X z v).const_smul (ε ^ n)
  refine (hzero.add hpos).congr hab (fun s _ => ?_) (fun s hs => ?_)
  · simp only [liftPolyField, Finset.sum_apply, Pi.smul_apply]
    rw [hrange, Finset.sum_insert h0mem]
  · have hcomp : ∀ n ∈ Finset.Icc 1 N,
        (cellOperator (Q.G s X) (Q.v s) (liftApply n (Cc hh n) (fun _ => f s) s X) z) v =
        cellOperator (Q.G s X) (Q.v s) (fun y => liftApply n (Cc hh n) (fun _ => f s) s X y v) z := by
      intro n hn
      have hbox := setting_lift_cross_field_box P sX sZ (by omega) Cc hseq hh hhh n
        (Finset.mem_Icc.1 hn).2 (f s) (hf s hs) s hs
      exact (cellOperator_postcomposition (ContinuousLinearMap.proj (R := ℝ) (φ := h) v)
        (Q.G s X) (Q.v s) (liftApply n (Cc hh n) (fun _ => f s) s X)
        ((hbox.1 X).of_le (by norm_num)) z).symm
    simp only [liftPositiveTimeRhs, liftPolyField, Finset.sum_apply, Pi.smul_apply, Pi.add_apply,
      Pi.neg_apply]
    have hR : (∑ n ∈ Finset.Icc 1 N, ε ^ n •
        (-cellOperator (Q.G s X) (Q.v s) (liftApply n (Cc hh n) (fun _ => f s) s X) z v +
          liftCellSource Q Cc (fun _ => f s) hh n s X z v)) =
        ∑ n ∈ Finset.Icc 1 N, ε ^ n •
          (-cellOperator (Q.G s X) (Q.v s) (fun y => liftApply n (Cc hh n) (fun _ => f s) s X y v) z +
            liftCellSource Q Cc (fun _ => f s) hh n s X z v) :=
      Finset.sum_congr rfl fun n hn => by rw [hcomp n hn]
    rw [hrange, Finset.sum_insert h0mem, hR]
    simp only [smul_add, Finset.sum_add_distrib]
    abel

include P in
/-- **`cycle_lift_identity` for a time-dependent coarse field** (component `v`): on the lift
window the truncated lift is of integral type with density the frozen-time right side of the
lift identity (cell operator, `εc ℬ₁`, `εc² ℬ₂`, sources, lifted means, explicit tail) at `f(s)`,
plus the lift of `ḟ(s)`. -/
theorem cycle_lift_identity_prim_td (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (ε : ℝ)
    (f df : ℝ → Vec 2 → ∀ i, h i) (hf : ∀ s ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (f s))
    (hjet : ∀ m, m ≤ N → ∀ (α : DerivativeWord2 m) (X : Vec 2) (u : ι),
      IsPrimOn a b (fun s => orderedDerivative α (f s) X u)
        (fun s => orderedDerivative α (df s) X u))
    (X z : Vec 2) (v : ι) :
    IsPrimOn a b (fun s => liftPolyField Cc N ε hh f s X z v)
      (fun s => (-(cellOperator (Q.G s X) (Q.v s) (liftPolyField Cc N ε hh (fun _ => f s) s X) z +
          ε • cellB1 Q.η Q.G Q.v s (liftPolyField Cc N ε hh (fun _ => f s) s) X z +
          ε ^ 2 • cellB2 Q.η Q.G s (liftPolyField Cc N ε hh (fun _ => f s) s) X z) +
        (if hh = 0 then 0 else sourceOp Q.edge Q.η ε s
          (liftPolyField Cc N ε (hh - 1) (fun _ => f s) s) X z) +
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
          liftPolyField Cc N ε p.1 (liftMeanPoly Q Cc N ε (fun _ => f s) p.2) s X z) +
        ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ n •
          liftTailCoeff Q Cc N (fun _ => f s) hh n s X z) v +
        liftPolyField Cc N ε hh df s X z v) :=
  (setting_liftPoly_prim_td P sX sZ hsX hsZ Cc hseq hh hhh ε f df hf hjet X z v).congr P.window
    (fun _ _ => rfl) (fun s hs => by
      rw [setting_liftPositiveTimeRhs_identity P sX sZ hsX hsZ Cc hseq hh hhh ε (f s) (hf s hs) s hs
        X z])
end

/-! **The lift identity in the label frame** (the lift is sampled at
`(𝗍, X, z) = (t/ℓ², y/ρ, y/e)`). At each label `y` the sampled truncated lift
of a time-dependent coarse field is of integral type in cell time; the cell operators
`𝒫₀ + εc ℬ₁ + εc² ℬ₂` sample to `ℓ²` times the label drift and the label diffusion
`w·∇_y − ν div_y(G ∇_y)` (`sample_cell_operators`), so the density is the label-frame operator
applied to the sampled lift plus the samples of the sources, the lifted means, the tail and the
lift of `ḟ`. -/

section
section Box

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isBoxSmooth_const_smul {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth sX sZ f)
    (c : ℝ) : IsBoxSmooth sX sZ (fun X z => c • f X z) :=
  hf.clm_comp (c • ContinuousLinearMap.id ℝ E)

theorem isBoxSmooth_finsetSum {κ : Type*} (s : Finset κ) {sX sZ : ℕ}
    {f : κ → Vec 2 → Vec 2 → E} (hf : ∀ k ∈ s, IsBoxSmooth sX sZ (f k)) :
    IsBoxSmooth sX sZ (fun X z => ∑ k ∈ s, f k X z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isBoxSmooth_zero (E := E) sX sZ
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hf k (Finset.mem_insert_self k s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end Box

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- The truncated lift of a smooth time-independent coarse field is box smooth at every time of
the window. -/
theorem setting_liftPolyField_box (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H) (ε : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (s : ℝ) (hs : s ∈ Icc a b)
    (hsZ : 1 ≤ sZ) :
    IsBoxSmooth 2 2 (liftPolyField Cc N ε hh (fun _ => f) s) :=
  isBoxSmooth_finsetSum _ fun n hn =>
    isBoxSmooth_const_smul (setting_lift_cross_field_box P sX sZ hsZ Cc hseq hh hhh n
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)) f hf s hs) _

include P in
/-- **The lift identity at a label.** At the label `y`, the sampled truncated lift of a
time-dependent coarse field is of integral type in cell time; its density is `-ℓ²` times the
label drift-diffusion operator applied to the sampled lift, plus the samples of the sources, the
lifted means, the tail and the lift of `ḟ` (component `v`). -/
theorem labels_lift_prim (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (ε : ℝ)
    (f df : ℝ → Vec 2 → ∀ i, h i) (hf : ∀ s ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (f s))
    (hjet : ∀ m, m ≤ N → ∀ (α : DerivativeWord2 m) (X : Vec 2) (u : ι),
      IsPrimOn a b (fun s => orderedDerivative α (f s) X u)
        (fun s => orderedDerivative α (df s) X u))
    (hG : ∀ s i j, Differentiable ℝ (fun X => Q.G s X i j))
    (w : ℝ → Vec 2 → Vec 2) {ρs es ℓsq νs c₁ : ℝ} (hv : ∀ s z, Q.v s z = c₁ • w s z)
    (h1 : ℓsq * νs * es⁻¹ * es⁻¹ = 1) (h2 : ε * Real.sqrt Q.η = ℓsq * νs * es⁻¹ * ρs⁻¹)
    (h3 : ε ^ 2 * Q.η = ℓsq * νs * ρs⁻¹ * ρs⁻¹) (hc : c₁ = ℓsq * es⁻¹)
    (y : Vec 2) (v : ι) :
    IsPrimOn a b (fun s => liftPolyField Cc N ε hh f s (ρs⁻¹ • y) (es⁻¹ • y) v)
      (fun s => (-(ℓsq • (∑ k, w s (es⁻¹ • y) k •
            fderiv ℝ (twoScaleSample ρs es (liftPolyField Cc N ε hh (fun _ => f s) s)) y
              (basisVec k)
          - νs • ∑ i, fderiv ℝ (fun y' => ∑ j, Q.G s (ρs⁻¹ • y') i j •
            fderiv ℝ (twoScaleSample ρs es (liftPolyField Cc N ε hh (fun _ => f s) s)) y'
              (basisVec j)) y (basisVec i))) +
        (if hh = 0 then 0 else sourceOp Q.edge Q.η ε s
          (liftPolyField Cc N ε (hh - 1) (fun _ => f s) s) (ρs⁻¹ • y) (es⁻¹ • y)) +
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
          liftPolyField Cc N ε p.1 (liftMeanPoly Q Cc N ε (fun _ => f s) p.2) s
            (ρs⁻¹ • y) (es⁻¹ • y)) +
        ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ n •
          liftTailCoeff Q Cc N (fun _ => f s) hh n s (ρs⁻¹ • y) (es⁻¹ • y)) v +
        liftPolyField Cc N ε hh df s (ρs⁻¹ • y) (es⁻¹ • y) v) := by
  refine (cycle_lift_identity_prim_td P sX sZ hsX hsZ Cc hseq hh hhh ε f df hf hjet
    (ρs⁻¹ • y) (es⁻¹ • y) v).congr P.window (fun _ _ => rfl) (fun s hs => ?_)
  have hΦ := setting_liftPolyField_box P sX sZ Cc hseq hh hhh ε (f s) (hf s hs) s hs
    (by omega)
  have hsample := sample_cell_operators hΦ Q.G Q.v s (hG s) (w s) (η := Q.η) (εc := ε)
    (ρ := ρs) (e := es) (ℓsq := ℓsq) (ν := νs) (c₁ := c₁) (hv s) h1 h2 h3 hc y
  simp only [twoScaleSample] at hsample
  rw [hsample]

include P in
/-- **The label-frame identity in physical time, summed over the grades.** With `c = ℓ²`, at
the label `y` the sampled lift `V(t, y) = ∑_{hh ≤ H} Φ_hh(t/c, y/ρ, y/e)` is of integral type on
the physical window `[c a, c b]`; its density is `-(w·∇_y − ν div_y G∇_y)V` plus `c⁻¹` times the
samples of the sources, the lifted means, the tail and the lift of `ḟ` (component `v`). -/
theorem labels_lift_prim_phys (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    (f df : ℝ → Vec 2 → ∀ i, h i) (hf : ∀ s ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (f s))
    (hjet : ∀ m, m ≤ N → ∀ (α : DerivativeWord2 m) (X : Vec 2) (u : ι),
      IsPrimOn a b (fun s => orderedDerivative α (f s) X u)
        (fun s => orderedDerivative α (df s) X u))
    (hG : ∀ s i j, Differentiable ℝ (fun X => Q.G s X i j))
    (w : ℝ → Vec 2 → Vec 2) {ρs es ℓsq νs c₁ : ℝ} (hℓ : 0 < ℓsq)
    (hv : ∀ s z, Q.v s z = c₁ • w s z)
    (h1 : ℓsq * νs * es⁻¹ * es⁻¹ = 1) (h2 : ε * Real.sqrt Q.η = ℓsq * νs * es⁻¹ * ρs⁻¹)
    (h3 : ε ^ 2 * Q.η = ℓsq * νs * ρs⁻¹ * ρs⁻¹) (hc : c₁ = ℓsq * es⁻¹)
    (y : Vec 2) (v : ι) :
    IsPrimOn (ℓsq * a) (ℓsq * b)
      (fun t => ∑ hh ∈ Finset.range (H + 1),
        liftPolyField Cc N ε hh f (ℓsq⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y) v)
      (fun t => ∑ hh ∈ Finset.range (H + 1), ℓsq⁻¹ • ((-(ℓsq • (∑ k, w (ℓsq⁻¹ * t) (es⁻¹ • y) k •
            fderiv ℝ (twoScaleSample ρs es
              (liftPolyField Cc N ε hh (fun _ => f (ℓsq⁻¹ * t)) (ℓsq⁻¹ * t))) y (basisVec k)
          - νs • ∑ i, fderiv ℝ (fun y' => ∑ j, Q.G (ℓsq⁻¹ * t) (ρs⁻¹ • y') i j •
            fderiv ℝ (twoScaleSample ρs es
              (liftPolyField Cc N ε hh (fun _ => f (ℓsq⁻¹ * t)) (ℓsq⁻¹ * t))) y' (basisVec j))
              y (basisVec i))) +
        (if hh = 0 then 0 else sourceOp Q.edge Q.η ε (ℓsq⁻¹ * t)
          (liftPolyField Cc N ε (hh - 1) (fun _ => f (ℓsq⁻¹ * t)) (ℓsq⁻¹ * t))
            (ρs⁻¹ • y) (es⁻¹ • y)) +
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
          liftPolyField Cc N ε p.1 (liftMeanPoly Q Cc N ε (fun _ => f (ℓsq⁻¹ * t)) p.2)
            (ℓsq⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y)) +
        ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ n •
          liftTailCoeff Q Cc N (fun _ => f (ℓsq⁻¹ * t)) hh n (ℓsq⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y)) v +
        liftPolyField Cc N ε hh df (ℓsq⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y) v)) := by
  have hab : a ≤ b := P.window
  have hℓi : 0 < ℓsq⁻¹ := inv_pos.2 hℓ
  have hA : a ≤ ℓsq⁻¹ * (ℓsq * a) := by rw [← mul_assoc, inv_mul_cancel₀ hℓ.ne', one_mul]
  have hB : ℓsq⁻¹ * (ℓsq * b) ≤ b := by rw [← mul_assoc, inv_mul_cancel₀ hℓ.ne', one_mul]
  refine IsPrimOn.sum (Finset.range (H + 1)) fun hh hh_mem => ?_
  have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hh_mem)
  exact (labels_lift_prim P sX sZ hsX hsZ Cc hseq hh hhh ε f df hf hjet hG w hv h1 h2 h3 hc
    y v).comp_mul hℓi (mul_le_mul_of_nonneg_left hab hℓ.le) hA hB
end

/-! **The label lift of a finite-rank coarse field read in the chart**. For the chart-frame field
`ã(𝗍, X) = a(c𝗍, χ(c𝗍, ρX))` of a finite-rank coarse field `a = ∑_k c_k(t) φ_k` (`chartField`), the
label lift `V(t, y) = ∑_{hh ≤ H} Φ_hh(t/c, y/ρ, y/e)` (`labelLift`) is, at every label `y`, of
integral type in physical time with the explicit density `labelDensity`: the label-frame
drift-diffusion operator applied to the lift, plus `c⁻¹` times the samples of the sources, the
lifted means, the tail and the lift of the material derivative of `a` read in the chart
(`chartFieldDot`). -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
/-- The chart-frame field of a finite-rank coarse field is smooth at every time. -/
theorem chartField_contDiff {κ : Type*} [Fintype κ] (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (χ : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2)) (c ρ s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (chartField cf φ χ c ρ s) := by
  have hpos : ContDiff ℝ (⊤ : ℕ∞) (fun X : Vec 2 => χ (c * s) (ρ • X)) :=
    hχ.comp (contDiff_const.prodMk ((contDiff_const (c := ρ)).smul contDiff_id))
  have he : chartField cf φ χ c ρ s = fun X => ∑ k, cf k (c * s) • φ k (χ (c * s) (ρ • X)) := rfl
  rw [he]
  exact ContDiff.sum fun k _ => (contDiff_const (c := cf k (c * s))).smul
    ((hφ k).comp hpos : ContDiff ℝ (⊤ : ℕ∞) (fun X => φ k (χ (c * s) (ρ • X))))

/-- The label lift `V(t, y) = ∑_{hh ≤ H} Φ_hh(t/c, y/ρ, y/e)` of the coarse field `f`. -/
def labelLift (Cc : ℕ → ℕ → LiftCoeff ι h) (N H : ℕ) (ε : ℝ) (f : ℝ → Vec 2 → ∀ i, h i)
    (ρs es ℓsq : ℝ) (t : ℝ) (y : Vec 2) : ∀ i, h i :=
  ∑ hh ∈ Finset.range (H + 1), liftPolyField Cc N ε hh f (ℓsq⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y)

/-- The physical-time density of the label lift (`labels_lift_prim_phys`), componentwise. -/
def labelDensity {D : ℕ} (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (N H : ℕ) (ε : ℝ) (f df : ℝ → Vec 2 → ∀ i, h i) (w : ℝ → Vec 2 → Vec 2)
    (ρs es ℓsq νs : ℝ) (t : ℝ) (y : Vec 2) : ∀ i, h i := fun v =>
  ∑ hh ∈ Finset.range (H + 1), ℓsq⁻¹ • ((-(ℓsq • (∑ k, w (ℓsq⁻¹ * t) (es⁻¹ • y) k •
        fderiv ℝ (twoScaleSample ρs es
          (liftPolyField Cc N ε hh (fun _ => f (ℓsq⁻¹ * t)) (ℓsq⁻¹ * t))) y (basisVec k)
      - νs • ∑ i, fderiv ℝ (fun y' => ∑ j, Q.G (ℓsq⁻¹ * t) (ρs⁻¹ • y') i j •
        fderiv ℝ (twoScaleSample ρs es
          (liftPolyField Cc N ε hh (fun _ => f (ℓsq⁻¹ * t)) (ℓsq⁻¹ * t))) y' (basisVec j))
          y (basisVec i))) +
    (if hh = 0 then 0 else sourceOp Q.edge Q.η ε (ℓsq⁻¹ * t)
      (liftPolyField Cc N ε (hh - 1) (fun _ => f (ℓsq⁻¹ * t)) (ℓsq⁻¹ * t))
        (ρs⁻¹ • y) (es⁻¹ • y)) +
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      liftPolyField Cc N ε p.1 (liftMeanPoly Q Cc N ε (fun _ => f (ℓsq⁻¹ * t)) p.2)
        (ℓsq⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y)) +
    ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ n •
      liftTailCoeff Q Cc N (fun _ => f (ℓsq⁻¹ * t)) hh n (ℓsq⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y)) v +
    liftPolyField Cc N ε hh df (ℓsq⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y) v)

variable {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **The label lift of a finite-rank coarse field read in the chart is of integral type.** At
every label `y` and component `v`, `t ↦ V(t, y)_v` is of integral type on the physical window
`[c a, c b]` with density `labelDensity` for the input `chartField` and its material derivative
`chartFieldDot`. -/
theorem labels_chart_prim (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (hφp : ∀ k, AVenhance.IsZ2Periodic (φ k))
    (χ W : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2))
    (hW : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => W p.1 p.2))
    (hχt : ∀ t y, HasDerivAt (fun t' => χ t' y) (W t (χ t y)) t)
    (hχl : ∀ t y (n : Fin 2 → ℤ), χ t (y + AVenhance.latticeShift n) =
      χ t y + AVenhance.latticeShift n)
    (hWp : ∀ t, AVenhance.IsZ2Periodic (W t))
    {c ρs : ℝ} (hc : 0 < c) (hρ : 0 < ρs) (A₀ B₀ : ℝ) (hA : A₀ ≤ c * a) (hB : c * b ≤ B₀)
    (hcf : ∀ k, IsPrimOn A₀ B₀ (cf k) (dcf k))
    (hG : ∀ s i j, Differentiable ℝ (fun X => Q.G s X i j))
    (w : ℝ → Vec 2 → Vec 2) {es νs c₁ : ℝ}
    (hv : ∀ s z, Q.v s z = c₁ • w s z)
    (h1 : c * νs * es⁻¹ * es⁻¹ = 1) (h2 : ε * Real.sqrt Q.η = c * νs * es⁻¹ * ρs⁻¹)
    (h3 : ε ^ 2 * Q.η = c * νs * ρs⁻¹ * ρs⁻¹) (hc₁ : c₁ = c * es⁻¹)
    (y : Vec 2) (v : ι) :
    IsPrimOn (c * a) (c * b)
      (fun t => labelLift Cc N H ε (chartField cf φ χ c ρs) ρs es c t y v)
      (fun t => labelDensity Q Cc N H ε (chartField cf φ χ c ρs)
        (chartFieldDot cf dcf φ χ W c ρs) w ρs es c νs t y v) := by
  have hab : a ≤ b := P.window
  have hprim := labels_lift_prim_phys P sX sZ hsX hsZ Cc hseq ε (chartField cf φ χ c ρs)
    (chartFieldDot cf dcf φ χ W c ρs)
    (fun s _ => chartField_contDiff cf φ hφ χ hχ c ρs s)
    (fun m _ α X u => chartField_jet_prim cf dcf φ hφ hφp χ W hχ hW hχt hχl hWp c ρs hc hρ
      A₀ B₀ a b hab hA hB hcf m α X u)
    hG w hc hv h1 h2 h3 hc₁ y v
  refine hprim.congr (mul_le_mul_of_nonneg_left hab hc.le) (fun t _ => ?_) (fun t _ => rfl)
  simp only [labelLift, Finset.sum_apply]
end

end AVRegularity.CycleComparison.Reconstruction
end
