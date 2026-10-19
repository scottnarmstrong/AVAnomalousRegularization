-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PathReduction.Premises
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleComparison.Error.WeakSolution

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleJointProofs.Assembly
namespace AVRegularity.CycleJointProofs.PathReduction

/-! Chosen homogeneous chain solutions and compatibility of their prefixes. -/

section
universe u v w x

variable (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (g₀ : ℝ) (H D Kmax Ks Ls Jm qJ Jchart : ℕ)
    (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (ρold : ℝ)

variable {α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb cMol cOld COld Crat
  Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold}

variable (hprem : JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart
      Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar
      π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold)

variable (hq : 1 < q) (hΛ : 128 ≤ Λ) (hζ : IsFastProfile ζ)
  (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)

/-- Identify periodic carriers at vertices known to be equal, as a linear map. -/
def torusVertexCast (J : ι → ℕ) (v v' : ι) (hv : v = v') :
    TorusHk (J v) (h v) →ₗ[ℝ] TorusHk (J v') (h v') := by
  subst v'
  exact LinearMap.id

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
@[simp] theorem torusVertexCast_refl (J : ι → ℕ) (v : ι) :
    torusVertexCast (h := h) J v v rfl = LinearMap.id := rfl

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- Vertex identification preserves the full factorial norm. -/
theorem torusVertexCast_norm (J : ι → ℕ) (v v' : ι) (hv : v = v') (ρ : ℝ)
    (f : TorusHk (J v) (h v)) :
    torusHkNorm ρ (le_refl (J v')) (torusVertexCast J v v' hv f) =
      torusHkNorm ρ (le_refl (J v)) f := by
  subst v'
  rfl

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- Vertex identification preserves every truncated factorial norm. -/
theorem torusVertexCast_order_norm (J : ι → ℕ) (L : ℕ) (hL : ∀ i, L ≤ J i)
    (v v' : ι) (hv : v = v') (ρ : ℝ) (f : TorusHk (J v) (h v)) :
    torusHkNorm ρ (hL v') (torusVertexCast J v v' hv f) = torusHkNorm ρ (hL v) f := by
  subst v'
  rfl

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- A vertex identification sends a section's value to its value at the identified vertex. -/
theorem torusVertexCast_apply_family (J : ι → ℕ) (v v' : ι) (hv : v = v')
    (f : ∀ i, TorusHk (J i) (h i)) : torusVertexCast J v v' hv (f v) = f v' := by
  subst v'
  rfl

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- Identifying a vertex preserves the error after truncating its higher-reserve model. -/
theorem torusVertexCast_error_norm (J : ι → ℕ) (Mout : ℕ)
    (v v' : ι) (hv : v = v') (ρ : ℝ)
    (u : TorusHk (J v) (h v)) (model : TorusHk (max Mout (J v)) (h v)) :
    torusHkNorm ρ (le_refl (J v'))
      (torusVertexCast J v v' hv u - truncateTorusHk (le_max_right Mout (J v'))
        (torusVertexCast (fun i => max Mout (J i)) v v' hv model)) =
      torusHkNorm ρ (le_refl (J v)) (u - truncateTorusHk (le_max_right Mout (J v)) model) := by
  subst v'
  rfl

/-- A chain trajectory with its Sobolev lift and its exact weak equation. -/
structure ChainSolution {n : ℕ} (p : Fin (n + 1) → ι)
    (f : ∀ k, TorusHk (K (p k)) (h (p k))) where
  u : ∀ k, ℝ → TorusHk (K (p k)) (h (p k))
  w : ∀ k, ℝ → TorusHk (K (p k) + 1) (h (p k))
  solution : IsCoupledWeakSolutionTorus ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D (K ∘ p)
    (edgeCoefficient (F.pathFamily p) ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual (K ∘ p))
    f (fun _ _ => 0) (fun _ _ => 0) u w

/-- Select a genuine chain solution supplied by the preparation existence theorem. -/
def chosenChainSolution {n : ℕ} (p : Fin (n + 1) → ι)
    (f : ∀ k, TorusHk (K (p k)) (h (p k))) :
    ChainSolution (α := α) (q := q) (Λ := Λ) (m := m) (Φ := Φ) (ν := ν) (tS := tS)
      (D := D) (K := K) (F := F) (actual := actual) p f :=
  Classical.choice (by
    obtain ⟨u, w, hs⟩ := preparation_path_exists_torus hprem hq hΛ hζ hchart hmol p f
    exact ⟨⟨u, w, hs⟩⟩)

/-- Equality of lower-order values determines higher-order lifts almost everywhere in time. -/
theorem torus_lifts_ae_eq {E₀ : Type*} [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀]
    [FiniteDimensional ℝ E₀] [MeasurableSpace E₀] [BorelSpace E₀] [CompleteSpace E₀]
    {k : ℕ} {a b : ℝ} (u u' : ℝ → TorusHk k E₀) (w w' : ℝ → TorusHk (k + 1) E₀)
    (hu : ∀ t ∈ Set.Icc a b, u t = u' t)
    (hw : ∀ᵐ t ∂volume.restrict (Set.Icc a b), truncateTorusHk (Nat.le_succ k) (w t) = u t)
    (hw' : ∀ᵐ t ∂volume.restrict (Set.Icc a b), truncateTorusHk (Nat.le_succ k) (w' t) = u' t) :
    w =ᵐ[volume.restrict (Set.Icc a b)] w' := by
  filter_upwards [hw, hw', ae_restrict_mem measurableSet_Icc] with t ht ht' htab
  apply TorusHk.ext_value
  have he : truncateTorusHk (Nat.le_succ k) (w t) = truncateTorusHk (Nat.le_succ k) (w' t) :=
    ht.trans ((hu t htab).trans ht'.symm)
  exact congrArg (fun z : TorusHk k E₀ => z.val (valueIndex2 k)) he

/-- Restricting a chosen chain to its prefix agrees with the separately chosen prefix trajectory. -/
theorem chosenChainSolution_prefix {n : ℕ} (p : Fin (n + 2) → ι)
    (f : ∀ k, TorusHk (K (p k)) (h (p k))) (k : Fin (n + 1))
    (t : ℝ) (ht : t ∈ Set.Icc tS (tS + 2 * ocTauPP α q Λ m)) :
    (chosenChainSolution hprem hq hΛ hζ hchart hmol p f).u k.castSucc t =
      (chosenChainSolution hprem hq hΛ hζ hchart hmol (p ∘ Fin.castSucc)
        (fun k => f k.castSucc)).u k t := by
  let S := chosenChainSolution hprem hq hΛ hζ hchart hmol p f
  let S' := chosenChainSolution hprem hq hΛ hζ hchart hmol (p ∘ Fin.castSucc)
    (fun k => f k.castSucc)
  exact preparation_path_unique hprem hq hΛ hchart hmol (p ∘ Fin.castSucc)
    (tS + 2 * ocTauPP α q Λ m)
    ⟨by have hh := hprem.cov.window; have hT := Construction.Stream.ocTauPP_pos
          (α := α) (q := q) (m := m) (show 1 ≤ Λ by omega); linarith, le_rfl⟩
    (fun k => f k.castSucc) (fun k => S.u k.castSucc) S'.u
    (fun k => S.w k.castSucc) S'.w
    (pathWeakSolution_prefix F ν _ _ actual K p tS _ (streamVel (Φ m)) f S.u S.w S.solution)
    S'.solution k t ht

/-- The Sobolev lifts of the chosen chain and prefix agree almost everywhere in time. -/
theorem chosenChainSolution_prefix_lift {n : ℕ} (p : Fin (n + 2) → ι)
    (f : ∀ k, TorusHk (K (p k)) (h (p k))) (k : Fin (n + 1)) :
    (chosenChainSolution hprem hq hΛ hζ hchart hmol p f).w k.castSucc =ᵐ[
      volume.restrict (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))]
      (chosenChainSolution hprem hq hΛ hζ hchart hmol (p ∘ Fin.castSucc)
        (fun k => f k.castSucc)).w k := by
  have hw := (chosenChainSolution hprem hq hΛ hζ hchart hmol p f).solution.2.2.1 k.castSucc
  have hw' := (chosenChainSolution hprem hq hΛ hζ hchart hmol (p ∘ Fin.castSucc)
      (fun k => f k.castSucc)).solution.2.2.1 k
  beta_reduce at hw hw'
  exact torus_lifts_ae_eq _ _ _ _
    (fun t ht => chosenChainSolution_prefix hprem hq hΛ hζ hchart hmol p f k t ht) hw hw'
omit [Fintype ι] [DecidableEq ι] in
/-- Restricting a datum supported at the first vertex to a prefix keeps it supported there. -/
private theorem pi_single_castSucc {n : ℕ} {M : Fin (n + 2) → Type*} [∀ k, Zero (M k)]
    (f : M 0) :
    (fun j : Fin (n + 1) => (Pi.single 0 f : ∀ k, M k) j.castSucc) =
      (Pi.single 0 f : ∀ j : Fin (n + 1), M j.castSucc) := by
  funext j
  by_cases hj : j = 0
  · subst j
    exact (Pi.single_eq_same (M := fun j : Fin (n + 1) => M j.castSucc) 0 f).symm
  · have hj' : j.castSucc ≠ 0 := by
      intro hh
      apply hj
      apply Fin.ext
      exact congrArg (fun z : Fin (n + 2) => z.val) hh
    rw [Pi.single_eq_of_ne (M := M) hj' f,
      Pi.single_eq_of_ne (M := fun k : Fin (n + 1) => M k.castSucc) hj f]

/-- Prefix compatibility for the datum supported at the first chain vertex. -/
theorem chosenChainSolution_single_prefix_lift {n : ℕ} (p : Fin (n + 2) → ι)
    (f : TorusHk (K (p 0)) (h (p 0))) (k : Fin (n + 1)) :
    (chosenChainSolution hprem hq hΛ hζ hchart hmol p (Pi.single 0 f)).w k.castSucc =ᵐ[
      volume.restrict (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))]
      (chosenChainSolution hprem hq hΛ hζ hchart hmol (p ∘ Fin.castSucc) (Pi.single 0 f)).w k := by
  have hd := pi_single_castSucc (M := fun k : Fin (n + 2) => TorusHk (K (p k)) (h (p k))) f
  have hh := chosenChainSolution_prefix_lift hprem hq hΛ hζ hchart hmol p (Pi.single 0 f) k
  have hq' := congrArg (fun fd : ∀ j : Fin (n + 1),
      TorusHk (K (p j.castSucc)) (h (p j.castSucc)) =>
      (chosenChainSolution hprem hq hΛ hζ hchart hmol (p ∘ Fin.castSucc) fd).w k) hd
  exact hh.trans (Filter.EventuallyEq.of_eq hq')

/-- A nontrivial chain's terminal row has exactly the forcing from its predecessor lift. -/
theorem chosenChainSolution_last_row {n : ℕ} (p : Fin (n + 2) → ι)
    (f : ∀ k, TorusHk (K (p k)) (h (p k))) :
    IsTorusRowSolution ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D
      (K (p (Fin.last (n + 1)))) (f (Fin.last (n + 1)))
      (fun t => (preparationCoefficientData hprem hq hΛ hchart hmol).edgeFlux
        (p (Fin.last (n + 1))) (p (Fin.last n).castSucc) t
        ((chosenChainSolution hprem hq hΛ hζ hchart hmol p f).w (Fin.last n).castSucc t))
      ((chosenChainSolution hprem hq hΛ hζ hchart hmol p f).u (Fin.last (n + 1)))
      ((chosenChainSolution hprem hq hΛ hζ hchart hmol p f).w (Fin.last (n + 1))) := by
  let S := chosenChainSolution hprem hq hΛ hζ hchart hmol p f
  let R := preparationCoefficientData hprem hq hΛ hchart hmol
  apply torusWeakSolution_row f S.u S.w S.solution (Fin.last (n + 1)) _
  intro t ht
  exact (R.edgeFlux_value_ae (p (Fin.last (n + 1))) (p (Fin.last n).castSucc) t ht
    (S.w (Fin.last n).castSucc t)).trans (Filter.Eventually.of_forall (fun x =>
      (pathRawFlux_last F ν _ _ actual K p (fun k => S.w k t) t x).symm))

/-- A nontrivial chain initialized at its source has zero terminal initial datum. -/
theorem chosenChainSolution_single_last_row {n : ℕ} (p : Fin (n + 2) → ι)
    (f : TorusHk (K (p 0)) (h (p 0))) :
    IsTorusRowSolution ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D
      (K (p (Fin.last (n + 1)))) 0
      (fun t => (preparationCoefficientData hprem hq hΛ hchart hmol).edgeFlux
        (p (Fin.last (n + 1))) (p (Fin.last n).castSucc) t
        ((chosenChainSolution hprem hq hΛ hζ hchart hmol p (Pi.single 0 f)).w
          (Fin.last n).castSucc t))
      ((chosenChainSolution hprem hq hΛ hζ hchart hmol p (Pi.single 0 f)).u (Fin.last (n + 1)))
      ((chosenChainSolution hprem hq hΛ hζ hchart hmol p (Pi.single 0 f)).w (Fin.last (n + 1))) := by
  have hs := chosenChainSolution_last_row hprem hq hΛ hζ hchart hmol p (Pi.single 0 f)
  have hne : Fin.last (n + 1) ≠ (0 : Fin (n + 2)) := by
    intro hh
    have he := congrArg (fun j : Fin (n + 2) => j.val) hh
    simp only [Fin.val_last, Fin.val_zero] at he
    omega
  have hf : (Pi.single 0 f : ∀ k, TorusHk (K (p k)) (h (p k))) (Fin.last (n + 1)) = 0 :=
    Pi.single_eq_of_ne hne _
  rw [hf] at hs
  exact hs

/-- A trivial chain is an unforced scalar row. -/
theorem chosenChainSolution_zero_row (p : Fin 1 → ι)
    (f : ∀ k, TorusHk (K (p k)) (h (p k))) :
    IsTorusRowSolution ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D
      (K (p 0)) (f 0) (fun _ => 0)
      ((chosenChainSolution hprem hq hΛ hζ hchart hmol p f).u 0)
      ((chosenChainSolution hprem hq hΛ hζ hchart hmol p f).w 0) := by
  let S := chosenChainSolution hprem hq hΛ hζ hchart hmol p f
  apply torusWeakSolution_row f S.u S.w S.solution 0 (fun _ => 0)
  intro t _
  exact (torusZero_rawJet_ae (K (p 0)) (valueIndex2 (K (p 0)))).trans
    (Filter.Eventually.of_forall (fun x => (pathRawFlux_zero F ν _ _ actual K p (fun k => S.w k t) t x).symm))

/-- Equal chronological vertex sequences give the same endpoint lift after vertex identification. -/
theorem chosenChainSolution_single_endpoint_congr {n : ℕ}
    (p p' : Fin (n + 1) → ι) (hpp : p = p') (v : ι)
    (hp : p (Fin.last n) = v) (hp' : p' (Fin.last n) = v)
    (f : ∀ i, TorusHk (K i) (h i)) (t : ℝ) :
    torusVertexCast (h := h) (fun i => K i + 1) _ v hp
      ((chosenChainSolution hprem hq hΛ hζ hchart hmol p (Pi.single 0 (f (p 0)))).w (Fin.last n) t) =
    torusVertexCast (h := h) (fun i => K i + 1) _ v hp'
      ((chosenChainSolution hprem hq hΛ hζ hchart hmol p' (Pi.single 0 (f (p' 0)))).w (Fin.last n) t) := by
  subst p'
  rfl
end

/-! Endpoint trajectories of backward paths and their finite expansion. -/

section
universe u v w x

variable (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (g₀ : ℝ) (H D Kmax Ks Ls Jm qJ Jchart : ℕ)
    (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad mStar : ℕ)
    {ι : Type u} [Fintype ι] [DecidableEq ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (K : ι → ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (M' : ℕ) (κ : ℕ → ℝ) (m : ℕ) (ν B : ℝ)
    (hφ : IsAdmissibleStream (Φ (m - 1))) (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
    {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx) (actual : ∀ p, Ctx p)
    (A : Matrix ι ι ℝ) (Θ : ℝ) (T : F.Atlas) (ρold : ℝ)

variable {α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart Ca Cth Cb cMol cOld COld Crat
  Cm CG Cchart Cpad Cage Npad mStar π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold}

variable (hprem : JointPremises α q Λ ζ g₀ H D Kmax Ks Ls Jm qJ Jchart
      Ca Cth Cb cMol cOld COld Crat Cm CG Cchart Cpad Cage Npad mStar
      π K Φ M' κ m ν B hφ tS g a B₀ lam l₀ P y₀ F actual A Θ T ρold)

variable (hq : 1 < q) (hΛ : 128 ≤ Λ) (hζ : IsFastProfile ζ)
  (hchart : Kmax + D + 2 ≤ Jchart) (hmol : Kmax + D + 2 ≤ Jm)

/-- Choose the chain with datum only at its first vertex. -/
def incomingChain {n : ℕ} (v : ι) (p : Incoming ι n)
    (f : ∀ i, TorusHk (K i) (h i)) :=
  chosenChainSolution hprem hq hΛ hζ hchart hmol (incomingVertices v p)
    (Pi.single 0 (f (incomingVertices v p 0)))

/-- The contribution of one path to its terminal component. -/
def incomingTrajectory {n : ℕ} (v : ι) (p : Incoming ι n)
    (f : ∀ i, TorusHk (K i) (h i)) : ℝ → TorusHk (K v) (h v) :=
  fun t => torusVertexCast (h := h) K _ v (incomingVertices_last v p)
    ((incomingChain hprem hq hΛ hζ hchart hmol v p f).u (Fin.last n) t)

/-- The high-order Sobolev lift of one path contribution. -/
def incomingLift {n : ℕ} (v : ι) (p : Incoming ι n)
    (f : ∀ i, TorusHk (K i) (h i)) : ℝ → TorusHk (K v + 1) (h v) :=
  fun t => torusVertexCast (h := h) (fun i => K i + 1) _ v (incomingVertices_last v p)
    ((incomingChain hprem hq hΛ hζ hchart hmol v p f).w (Fin.last n) t)

/-- The incoming forcing of a path uses the lift of its prefix. -/
def incomingForcing : ∀ {n : ℕ}, (v : ι) → Incoming ι n →
    (∀ i, TorusHk (K i) (h i)) → ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v))
  | 0, _, _, _ => fun _ => 0
  | _ + 1, v, p, f => fun t =>
    (preparationCoefficientData hprem hq hΛ hchart hmol).edgeFlux v p.1 t
      (incomingLift hprem hq hΛ hζ hchart hmol p.1 p.2 f t)

/-- Only a path of length zero contributes an initial value at its terminal vertex. -/
def incomingInitial : ∀ {n : ℕ}, (v : ι) → Incoming ι n →
    (∀ i, TorusHk (K i) (h i)) → TorusHk (K v) (h v)
  | 0, v, _, f => f v
  | _ + 1, _, _, _ => 0

omit [Fintype ι] [DecidableEq ι] in
/-- Vertex identifications preserve a scalar row and identify its incoming flux carrier. -/
theorem torusRowSolution_vertexCast (ν a b : ℝ) (vfield : ℝ → Vec 2 → Vec 2)
    (D : ℕ) (v v' : ι) (hv : v = v') (f : TorusHk (K v) (h v))
    (Q : ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v)))
    (u : ℝ → TorusHk (K v) (h v)) (w : ℝ → TorusHk (K v + 1) (h v))
    (hs : IsTorusRowSolution ν a b vfield D (K v) f Q u w) :
    IsTorusRowSolution ν a b vfield D (K v') (torusVertexCast K v v' hv f)
      (fun t => torusVertexCast (h := fun i => PiLp 2 (fun _ : Fin 2 => h i)) K v v' hv (Q t))
      (fun t => torusVertexCast K v v' hv (u t))
      (fun t => torusVertexCast (fun i => K i + 1) v v' hv (w t)) := by
  subst v'
  exact hs

/-- The predecessor lift of a longer chain is the endpoint lift of its shorter prefix. -/
theorem incomingChain_prefix_lift {n : ℕ} (v : ι) (p : ι × Incoming ι n)
    (f : ∀ i, TorusHk (K i) (h i)) :
    (fun t => torusVertexCast (h := h) (fun i => K i + 1)
      (incomingVertices (n := n + 1) v p (Fin.last n).castSucc) p.1
      (by simp only [incomingVertices, Fin.lastCases_castSucc, incomingVertices_last])
      ((incomingChain (n := n + 1) hprem hq hΛ hζ hchart hmol v p f).w (Fin.last n).castSucc t)) =ᵐ[
      volume.restrict (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))]
      incomingLift hprem hq hΛ hζ hchart hmol p.1 p.2 f := by
  have hh := chosenChainSolution_single_prefix_lift hprem hq hΛ hζ hchart hmol
    (incomingVertices (n := n + 1) v p) (f (incomingVertices (n := n + 1) v p 0)) (Fin.last n)
  have hp : incomingVertices (n := n + 1) v p ∘ Fin.castSucc = incomingVertices p.1 p.2 := by
    funext j
    simp only [Function.comp_apply, incomingVertices, Fin.lastCases_castSucc]
  filter_upwards [hh] with t ht
  have he := congrArg
    (fun z => torusVertexCast (h := h) (fun i => K i + 1)
      (incomingVertices (n := n + 1) v p (Fin.last n).castSucc) p.1
      (by simp only [incomingVertices, Fin.lastCases_castSucc, incomingVertices_last]) z) ht
  exact he.trans (chosenChainSolution_single_endpoint_congr hprem hq hΛ hζ hchart hmol
    (incomingVertices (n := n + 1) v p ∘ Fin.castSucc) (incomingVertices p.1 p.2) hp p.1
    (by simp only [Function.comp_apply, incomingVertices, Fin.lastCases_castSucc, incomingVertices_last])
    (incomingVertices_last p.1 p.2) f t : _)

omit [Fintype ι] [DecidableEq ι] in
/-- Identifying either endpoint of an edge commutes with its physical forcing carrier. -/
theorem TorusCoefficientData.edgeFlux_vertexCast {r a b : ℝ}
    {Acoef : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)}
    (R : TorusCoefficientData (h := h) r K D a b Acoef)
    (v v' u u' : ι) (hv : v = v') (hu : u = u') (t : ℝ)
    (w : TorusHk (K u + 1) (h u)) :
    torusVertexCast (h := fun i => PiLp 2 (fun _ : Fin 2 => h i)) K v v' hv (R.edgeFlux v u t w) =
      R.edgeFlux v' u' t (torusVertexCast (h := h) (fun i => K i + 1) u u' hu w) := by
  subst v'
  subst u'
  rfl

/-- A path of length zero solves the unforced scalar row. -/
theorem incoming_zero_row_solution (v : ι) (p : Incoming ι 0)
    (f : ∀ i, TorusHk (K i) (h i)) :
    IsTorusRowSolution ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D (K v)
      (incomingInitial v p f) (incomingForcing hprem hq hΛ hζ hchart hmol v p f)
      (incomingTrajectory hprem hq hΛ hζ hchart hmol v p f)
      (incomingLift hprem hq hΛ hζ hchart hmol v p f) := by
  have hs := chosenChainSolution_zero_row hprem hq hΛ hζ hchart hmol (fun _ : Fin 1 => v)
    (Pi.single 0 (f v))
  have hu : incomingTrajectory hprem hq hΛ hζ hchart hmol v p f =
      (chosenChainSolution hprem hq hΛ hζ hchart hmol (fun _ : Fin 1 => v)
        (Pi.single 0 (f v))).u 0 := by
    funext t
    unfold incomingTrajectory incomingChain
    simp only [incomingVertices, torusVertexCast_refl]
    rfl
  have hw : incomingLift hprem hq hΛ hζ hchart hmol v p f =
      (chosenChainSolution hprem hq hΛ hζ hchart hmol (fun _ : Fin 1 => v)
        (Pi.single 0 (f v))).w 0 := by
    funext t
    unfold incomingLift incomingChain
    simp only [incomingVertices, torusVertexCast_refl]
    rfl
  simpa only [incomingInitial, incomingForcing, hu, hw, Pi.single_eq_same] using hs

omit [Fintype ι] [DecidableEq ι] in
/-- Vertex identifications of a row forced by one edge flux, over arbitrary vertices. -/
private theorem torusRowSolution_vertexCast_edgeFlux {r a b : ℝ}
    {Acoef : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)}
    (R : TorusCoefficientData (h := h) r K D a b Acoef) (ν : ℝ) (vfield : ℝ → Vec 2 → Vec 2)
    (v₀ v u₀ u : ι) (hv : v₀ = v) (hu : u₀ = u) (W : ℝ → TorusHk (K u₀ + 1) (h u₀))
    (U : ℝ → TorusHk (K v₀) (h v₀)) (Wl : ℝ → TorusHk (K v₀ + 1) (h v₀))
    (hs : IsTorusRowSolution ν a b vfield D (K v₀) 0 (fun t => R.edgeFlux v₀ u₀ t (W t)) U Wl) :
    IsTorusRowSolution ν a b vfield D (K v) 0
      (fun t => R.edgeFlux v u t (torusVertexCast (h := h) (fun i => K i + 1) u₀ u hu (W t)))
      (fun t => torusVertexCast K v₀ v hv (U t))
      (fun t => torusVertexCast (fun i => K i + 1) v₀ v hv (Wl t)) := by
  subst hv
  subst hu
  exact hs

/-- A longer path solves its row with precisely the forcing from its shorter prefix. -/
theorem incoming_succ_predecessor_row_solution {n : ℕ} (v : ι) (p : Incoming ι (n + 1))
    (f : ∀ i, TorusHk (K i) (h i)) :
    IsTorusRowSolution ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D (K v)
      0 (fun t => (preparationCoefficientData hprem hq hΛ hchart hmol).edgeFlux v p.1 t
        (torusVertexCast (h := h) (fun i => K i + 1)
          (incomingVertices (n := n + 1) v p (Fin.last n).castSucc) p.1
          (by simp only [incomingVertices, Fin.lastCases_castSucc, incomingVertices_last])
          ((incomingChain hprem hq hΛ hζ hchart hmol v p f).w (Fin.last n).castSucc t)))
      (incomingTrajectory hprem hq hΛ hζ hchart hmol v p f)
      (incomingLift hprem hq hΛ hζ hchart hmol v p f) := by
  have hpred : incomingVertices (n := n + 1) v p (Fin.last n).castSucc = p.1 := by
    simp only [incomingVertices, Fin.lastCases_castSucc, incomingVertices_last]
  exact torusRowSolution_vertexCast_edgeFlux (preparationCoefficientData hprem hq hΛ hchart hmol)
    ν (streamVel (Φ m)) _ v _ p.1 (incomingVertices_last (n := n + 1) v p) hpred _ _ _
    (chosenChainSolution_single_last_row hprem hq hΛ hζ hchart hmol
      (incomingVertices (n := n + 1) v p) (f (incomingVertices (n := n + 1) v p 0)))

/-- The predecessor lift can be replaced by the shorter chain lift in the row equation. -/
theorem incoming_succ_row_solution {n : ℕ} (v : ι) (p : Incoming ι (n + 1))
    (f : ∀ i, TorusHk (K i) (h i)) :
    IsTorusRowSolution ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D (K v)
      (incomingInitial v p f) (incomingForcing hprem hq hΛ hζ hchart hmol v p f)
      (incomingTrajectory hprem hq hΛ hζ hchart hmol v p f)
      (incomingLift hprem hq hΛ hζ hchart hmol v p f) := by
  have hs := incoming_succ_predecessor_row_solution hprem hq hΛ hζ hchart hmol v p f
  apply torusRowSolution_forcing_congr ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m))
    D (K v) 0 _ _ _ _ ?_ hs
  filter_upwards [incomingChain_prefix_lift hprem hq hΛ hζ hchart hmol v p f] with t ht
  exact congrArg ((preparationCoefficientData hprem hq hΛ hchart hmol).edgeFlux v p.1 t) ht

/-- Every path contribution solves its scalar row with the forcing of its shorter prefix. -/
theorem incoming_row_solution {n : ℕ} (v : ι) (p : Incoming ι n)
    (f : ∀ i, TorusHk (K i) (h i)) :
    IsTorusRowSolution ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D (K v)
      (incomingInitial v p f) (incomingForcing hprem hq hΛ hζ hchart hmol v p f)
      (incomingTrajectory hprem hq hΛ hζ hchart hmol v p f)
      (incomingLift hprem hq hΛ hζ hchart hmol v p f) := by
  cases n with
  | zero => exact incoming_zero_row_solution hprem hq hΛ hζ hchart hmol v p f
  | succ n => exact incoming_succ_row_solution hprem hq hΛ hζ hchart hmol v p f

include hprem hq hΛ hchart hmol in
/-- Uniqueness of the trivial chain makes a zero-data, unforced row vanish. -/
theorem preparation_unforced_row_zero (v : ι)
    (u : ℝ → TorusHk (K v) (h v)) (w : ℝ → TorusHk (K v + 1) (h v))
    (hs : IsTorusRowSolution ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m))
      D (K v) 0 (fun _ => 0) u w) :
    ∀ t ∈ Set.Icc tS (tS + 2 * ocTauPP α q Λ m), u t = 0 := by
  let p : Fin 1 → ι := fun _ => v
  have hcoeff : edgeCoefficient (F.pathFamily p) ν (ocEpsilon q Λ m)
      (ocEpsilon q Λ (m - 1)) actual (K ∘ p) = (fun _ _ _ _ _ => 0) := by
    funext i j d t x
    have hij : i.val ≠ j.val + 1 := by
      have hi := i.isLt
      have hj := j.isLt
      omega
    exact congrFun (congrFun (path_edgeCoefficient_zero F p ν _ _ actual K i j hij d) t) x
  have hs0 : IsTorusRowSolution (E := h v) ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m))
      D (K v) 0 (fun _ => 0) (fun _ => 0) (fun _ => 0) := by
    have hh := CycleComparison.Error.isCoupledWeakSolutionTorus_sub hs hs
    simpa only [IsTorusRowSolution, sub_self] using hh
  have hT : tS ≤ tS + 2 * ocTauPP α q Λ m := by
    have hh := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) (show 1 ≤ Λ by omega)
    linarith only [hh]
  have hh := preparation_path_unique hprem hq hΛ hchart hmol p
    (tS + 2 * ocTauPP α q Λ m) ⟨hT, le_rfl⟩ (fun _ => 0)
    (fun _ => u) (fun _ _ => 0) (fun _ => w) (fun _ _ => 0)
    (by rw [hcoeff]; exact (hs : _)) (by rw [hcoeff]; exact (hs0 : _))
  exact hh 0

/-- Vanishing terminal values also identify their high-order lifts with zero. -/
theorem incomingLift_zero_of_trajectory_zero {n : ℕ} (v : ι) (p : Incoming ι n)
    (f : ∀ i, TorusHk (K i) (h i))
    (hu : ∀ t ∈ Set.Icc tS (tS + 2 * ocTauPP α q Λ m),
      incomingTrajectory hprem hq hΛ hζ hchart hmol v p f t = 0) :
    incomingLift hprem hq hΛ hζ hchart hmol v p f =ᵐ[
      volume.restrict (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))] (fun _ => 0) := by
  have hs := incoming_row_solution hprem hq hΛ hζ hchart hmol v p f
  have hw := hs.2.2.1 0
  beta_reduce at hw
  apply torus_lifts_ae_eq _ (fun _ => 0) _ (fun _ => 0) hu hw
  exact Filter.Eventually.of_forall (fun _ => (truncateTorusHk (E := h v) (Nat.le_succ (K v))).map_zero)

/-- A missing edge or a zero envelope entry produces the zero forcing carrier. -/
theorem preparation_invalid_edgeFlux_zero (v u : ι)
    (he : ¬ Nonempty (F.Γ v u) ∨ ¬ 0 < A v u) (t : ℝ)
    (w : TorusHk (K u + 1) (h u)) :
    (preparationCoefficientData hprem hq hΛ hchart hmol).edgeFlux v u t w = 0 := by
  apply TorusCoefficientData.edgeFlux_of_zero
  intro d s hs x
  rcases he with he | he
  · exact congrFun (congrFun (physicalCoefficient_zero_of_no_edge F ν
      (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual v u d.val he) s) x
  · have hA : 0 ≤ A v u := (mul_nonneg_iff_of_pos_left
        (Real.sqrt_pos.mpr (div_pos (hprem.hπ u) (hprem.hπ v)))).mp (hprem.henv.nonneg v u)
    have hz : A v u = 0 := le_antisymm (le_of_not_gt he) hA
    exact preparation_edge_zero hprem hq hΛ hchart hmol v u hz d s hs x

/-- Every path with a missing or zero edge has identically zero endpoint trajectory. -/
theorem incoming_invalid_trajectory_zero {n : ℕ} (v : ι) (p : Incoming ι n)
    (f : ∀ i, TorusHk (K i) (h i)) (hp : ¬ IncomingValid F A v p) :
    ∀ t ∈ Set.Icc tS (tS + 2 * ocTauPP α q Λ m),
      incomingTrajectory hprem hq hΛ hζ hchart hmol v p f t = 0 := by
  classical
  induction n generalizing v with
  | zero => exact False.elim (hp trivial)
  | succ n ih =>
    have hQ : incomingForcing hprem hq hΛ hζ hchart hmol v p f =ᵐ[
        volume.restrict (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))] (fun _ => 0) := by
      by_cases he : Nonempty (F.Γ v p.1) ∧ 0 < A v p.1
      · have hprefix : ¬ IncomingValid F A p.1 p.2 := fun hh => hp ⟨he.1, he.2, hh⟩
        have hl := incomingLift_zero_of_trajectory_zero hprem hq hΛ hζ hchart hmol
          p.1 p.2 f (ih p.1 p.2 hprefix)
        filter_upwards [hl] with t ht
        change (preparationCoefficientData hprem hq hΛ hchart hmol).edgeFlux v p.1 t
          (incomingLift hprem hq hΛ hζ hchart hmol p.1 p.2 f t) = 0
        rw [ht, TorusCoefficientData.edgeFlux_zero]
      · exact Filter.Eventually.of_forall (fun t =>
          preparation_invalid_edgeFlux_zero hprem hq hΛ hchart hmol v p.1
            (not_and_or.mp he) t (incomingLift hprem hq hΛ hζ hchart hmol p.1 p.2 f t))
    have hs := torusRowSolution_forcing_congr ν tS (tS + 2 * ocTauPP α q Λ m)
      (streamVel (Φ m)) D (K v) 0 _ (fun _ => 0) _ _ hQ
      (incoming_row_solution hprem hq hΛ hζ hchart hmol v p f)
    exact preparation_unforced_row_zero hprem hq hΛ hchart hmol v _ _ hs

/-- A constant backward path witnesses nonemptiness of every path set ending at a vertex. -/
def incomingConstant {J : Type*} (v : J) : (n : ℕ) → Incoming J n
  | 0 => PUnit.unit
  | n + 1 => (v, incomingConstant v n)

/-- Sum of endpoint contributions of a fixed length. -/
def incomingSum (n : ℕ) (v : ι) (f : ∀ i, TorusHk (K i) (h i)) :
    ℝ → TorusHk (K v) (h v) :=
  fun t => ∑ p : Incoming ι n, incomingTrajectory hprem hq hΛ hζ hchart hmol v p f t

/-- High-order lift of the sum of endpoint contributions of a fixed length. -/
def incomingSumLift (n : ℕ) (v : ι) (f : ∀ i, TorusHk (K i) (h i)) :
    ℝ → TorusHk (K v + 1) (h v) :=
  fun t => ∑ p : Incoming ι n, incomingLift hprem hq hΛ hζ hchart hmol v p f t

/-- Sum of the initial values of all paths of a fixed length. -/
def incomingSumInitial (n : ℕ) (v : ι) (f : ∀ i, TorusHk (K i) (h i)) :=
  ∑ p : Incoming ι n, incomingInitial v p f

/-- Sum of the external row fluxes of all paths of a fixed length. -/
def incomingSumForcing (n : ℕ) (v : ι) (f : ∀ i, TorusHk (K i) (h i)) :=
  fun t => ∑ p : Incoming ι n, incomingForcing hprem hq hΛ hζ hchart hmol v p f t

/-- Superposition gives the row equation of all paths of one length. -/
theorem incoming_sum_row_solution (n : ℕ) (v : ι) (f : ∀ i, TorusHk (K i) (h i)) :
    IsTorusRowSolution ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D (K v)
      (incomingSumInitial n v f) (incomingSumForcing hprem hq hΛ hζ hchart hmol n v f)
      (incomingSum hprem hq hΛ hζ hchart hmol n v f)
      (incomingSumLift hprem hq hΛ hζ hchart hmol n v f) := by
  exact torusRowSolution_finset_sum ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m))
    D (K v) (fun p => incomingInitial v p f)
    (fun p => incomingForcing hprem hq hΛ hζ hchart hmol v p f)
    (fun p => incomingTrajectory hprem hq hΛ hζ hchart hmol v p f)
    (fun p => incomingLift hprem hq hΛ hζ hchart hmol v p f)
    (fun p => incoming_row_solution hprem hq hΛ hζ hchart hmol v p f)
    Finset.univ ⟨incomingConstant v n, Finset.mem_univ _⟩

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- Exactly the trivial paths supply the original datum. -/
theorem incoming_sum_initial_zero (v : ι) (f : ∀ i, TorusHk (K i) (h i)) :
    incomingSumInitial 0 v f = f v := by
  change (∑ _ : PUnit, f v) = f v
  exact Fintype.sum_unique _

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- Positive-length paths have zero terminal initial datum. -/
theorem incoming_sum_initial_succ (n : ℕ) (v : ι) (f : ∀ i, TorusHk (K i) (h i)) :
    incomingSumInitial (n + 1) v f = 0 := by
  simp only [incomingSumInitial, incomingInitial, Finset.sum_const_zero]

/-- The trivial paths have zero external forcing. -/
theorem incoming_sum_forcing_zero (v : ι) (f : ∀ i, TorusHk (K i) (h i)) (t : ℝ) :
    incomingSumForcing hprem hq hΛ hζ hchart hmol 0 v f t = 0 := by
  simp only [incomingSumForcing, incomingForcing, Finset.sum_const_zero]

/-- Adding the terminal vertex sums the incoming fluxes of the shorter paths. -/
theorem incoming_sum_forcing_succ (n : ℕ) (v : ι) (f : ∀ i, TorusHk (K i) (h i)) (t : ℝ) :
    incomingSumForcing hprem hq hΛ hζ hchart hmol (n + 1) v f t =
      ∑ u, (preparationCoefficientData hprem hq hΛ hchart hmol).edgeFlux v u t
        (incomingSumLift hprem hq hΛ hζ hchart hmol n u f t) := by
  change (∑ p : ι × Incoming ι n,
      (preparationCoefficientData hprem hq hΛ hchart hmol).edgeFlux v p.1 t
        (incomingLift hprem hq hΛ hζ hchart hmol p.1 p.2 f t)) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  exact ((preparationCoefficientData hprem hq hΛ hchart hmol).edgeFlux_sum v u t
    Finset.univ (fun p => incomingLift hprem hq hΛ hζ hchart hmol u p f t)).symm

/-- An invalid positive-length path also has zero incoming forcing almost everywhere. -/
theorem incoming_invalid_forcing_zero {n : ℕ} (v : ι) (p : Incoming ι (n + 1))
    (f : ∀ i, TorusHk (K i) (h i)) (hp : ¬ IncomingValid F A v p) :
    incomingForcing hprem hq hΛ hζ hchart hmol v p f =ᵐ[
      volume.restrict (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))] (fun _ => 0) := by
  classical
  by_cases he : Nonempty (F.Γ v p.1) ∧ 0 < A v p.1
  · have hprefix : ¬ IncomingValid F A p.1 p.2 := fun hh => hp ⟨he.1, he.2, hh⟩
    have hl := incomingLift_zero_of_trajectory_zero hprem hq hΛ hζ hchart hmol
      p.1 p.2 f (incoming_invalid_trajectory_zero hprem hq hΛ hζ hchart hmol p.1 p.2 f hprefix)
    filter_upwards [hl] with t ht
    change (preparationCoefficientData hprem hq hΛ hchart hmol).edgeFlux v p.1 t
      (incomingLift hprem hq hΛ hζ hchart hmol p.1 p.2 f t) = 0
    rw [ht, TorusCoefficientData.edgeFlux_zero]
  · exact Filter.Eventually.of_forall (fun t =>
      preparation_invalid_edgeFlux_zero hprem hq hΛ hchart hmol v p.1
        (not_and_or.mp he) t (incomingLift hprem hq hΛ hζ hchart hmol p.1 p.2 f t))

/-- Depth removes the forcing at the first omitted path length. -/
theorem incoming_sum_forcing_cutoff (v : ι) (f : ∀ i, TorusHk (K i) (h i)) :
    incomingSumForcing hprem hq hΛ hζ hchart hmol (H + 1) v f =ᵐ[
      volume.restrict (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))] (fun _ => 0) := by
  have hall := ae_all_iff.mpr (fun p : Incoming ι (H + 1) =>
    incoming_invalid_forcing_zero hprem hq hΛ hζ hchart hmol v p f
      (fun hh => (Nat.not_succ_le_self H) (incomingValid_length F A hprem.hdepth v p hh)))
  filter_upwards [hall] with t ht
  exact (Finset.sum_eq_zero (s := Finset.univ) (fun p _ => ht p) : _)

/-- The finite path expansion, with one contribution at every length through the depth. -/
def allIncoming (v : ι) (f : ∀ i, TorusHk (K i) (h i)) : ℝ → TorusHk (K v) (h v) :=
  fun t => ∑ n ∈ Finset.range (H + 1), incomingSum hprem hq hΛ hζ hchart hmol n v f t

/-- High-order lift of the finite path expansion. -/
def allIncomingLift (v : ι) (f : ∀ i, TorusHk (K i) (h i)) : ℝ → TorusHk (K v + 1) (h v) :=
  fun t => ∑ n ∈ Finset.range (H + 1), incomingSumLift hprem hq hΛ hζ hchart hmol n v f t

/-- The shifted length sum uses the same indices once its endpoint terms vanish. -/
theorem sum_range_shift_of_zero {E : Type*} [AddCommMonoid E] (Q : ℕ → E) (n : ℕ)
    (h0 : Q 0 = 0) (hn : Q n = 0) :
    (∑ j ∈ Finset.range n, Q j) = ∑ j ∈ Finset.range n, Q (j + 1) := by
  have hleft := Finset.sum_range_succ Q n
  have hright := Finset.sum_range_succ' Q n
  rw [hn, add_zero] at hleft
  rw [h0, add_zero] at hright
  exact hleft.symm.trans hright

omit [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- Summing all lengths keeps exactly the original initial datum. -/
theorem allIncoming_initial (v : ι) (f : ∀ i, TorusHk (K i) (h i)) :
    (∑ n ∈ Finset.range (H + 1), incomingSumInitial n v f) = f v := by
  classical
  rw [Finset.sum_eq_single 0]
  · exact incoming_sum_initial_zero v f
  · intro n _ hn
    cases n with
    | zero => exact False.elim (hn rfl)
    | succ n => exact incoming_sum_initial_succ n v f
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr (Nat.zero_lt_succ H)))

/-- The total external forcing agrees almost everywhere with the full incoming coupling. -/
theorem allIncoming_forcing (v : ι) (f : ∀ i, TorusHk (K i) (h i)) :
    (fun t => ∑ n ∈ Finset.range (H + 1),
      incomingSumForcing hprem hq hΛ hζ hchart hmol n v f t) =ᵐ[
      volume.restrict (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))]
    (fun t => ∑ u, (preparationCoefficientData hprem hq hΛ hchart hmol).edgeFlux v u t
      (allIncomingLift (H := H) hprem hq hΛ hζ hchart hmol u f t)) := by
  filter_upwards [incoming_sum_forcing_cutoff hprem hq hΛ hζ hchart hmol v f] with t ht
  rw [sum_range_shift_of_zero _ (H + 1)
    (incoming_sum_forcing_zero hprem hq hΛ hζ hchart hmol v f t) ht]
  simp_rw [incoming_sum_forcing_succ hprem hq hΛ hζ hchart hmol]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  exact ((preparationCoefficientData hprem hq hΛ hchart hmol).edgeFlux_sum v u t
    (Finset.range (H + 1))
    (fun n => incomingSumLift hprem hq hΛ hζ hchart hmol n u f t)).symm

/-- The finite expansion solves each scalar row of the original family. -/
theorem allIncoming_row_solution (v : ι) (f : ∀ i, TorusHk (K i) (h i)) :
    IsTorusRowSolution ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D (K v)
      (f v) (fun t => ∑ u, (preparationCoefficientData hprem hq hΛ hchart hmol).edgeFlux v u t
        (allIncomingLift (H := H) hprem hq hΛ hζ hchart hmol u f t))
      (allIncoming (H := H) hprem hq hΛ hζ hchart hmol v f)
      (allIncomingLift (H := H) hprem hq hΛ hζ hchart hmol v f) := by
  have hs := torusRowSolution_finset_sum ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m))
    D (K v) (fun n => incomingSumInitial n v f)
    (fun n => incomingSumForcing hprem hq hΛ hζ hchart hmol n v f)
    (fun n => incomingSum hprem hq hΛ hζ hchart hmol n v f)
    (fun n => incomingSumLift hprem hq hΛ hζ hchart hmol n v f)
    (fun n => incoming_sum_row_solution hprem hq hΛ hζ hchart hmol n v f)
    (Finset.range (H + 1)) ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ H)⟩
  rw [allIncoming_initial] at hs
  exact torusRowSolution_forcing_congr ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m))
    D (K v) (f v) _ _ _ _ (allIncoming_forcing hprem hq hΛ hζ hchart hmol v f) hs

/-- The finite expansion is a genuine homogeneous solution of the original coupled family. -/
theorem allIncoming_solution (f : ∀ i, TorusHk (K i) (h i)) :
    IsCoupledWeakSolutionTorus ν tS (tS + 2 * ocTauPP α q Λ m) (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      f (fun _ _ => 0) (fun _ _ => 0)
      (fun i => allIncoming (H := H) hprem hq hΛ hζ hchart hmol i f)
      (fun i => allIncomingLift (H := H) hprem hq hΛ hζ hchart hmol i f) := by
  exact torusWeakSolution_of_rows f _ _ _
    (fun i => allIncoming_row_solution hprem hq hΛ hζ hchart hmol i f)
    (fun i t ht => (preparationCoefficientData hprem hq hΛ hchart hmol).totalFlux_value_ae
      i t ht (fun j => allIncomingLift (H := H) hprem hq hΛ hζ hchart hmol j f t))

/-- Every solution on an initial subwindow has the finite path expansion. -/
theorem preparation_path_expansion (τ : ℝ)
    (hτ : τ ∈ Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
    (f : ∀ i, TorusHk (K i) (h i))
    (u : ∀ i, ℝ → TorusHk (K i) (h i)) (w : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionTorus ν tS τ (streamVel (Φ m)) D K
      (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K)
      f (fun _ _ => 0) (fun _ _ => 0) u w) :
    ∀ i, ∀ t ∈ Set.Icc tS τ,
      u i t = allIncoming (H := H) hprem hq hΛ hζ hchart hmol i f t := by
  exact preparation_unique hprem hq hΛ hchart hmol τ hτ f u _ w _ hs
    (CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_left hτ.2
      (allIncoming_solution hprem hq hΛ hζ hchart hmol f))
end

/-! Corner operators of the core applied to a chain, and their entrywise estimates. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- One application of the raw core, retaining model and error for the same operator. -/
structure ChainCore (F : ChartedFamily ι h D P Ctx) (actual : ∀ a, Ctx a)
    (K : ι → ℕ) (Mout : ℕ) (ν e E tS tp ρs ρold ρm Pacc C CP : ℝ)
    (b : ℝ → Vec 2 → Vec 2) {n : ℕ} (p : Fin (n + 1) → ι) (πp : Fin (n + 1) → ℝ) where
  operator : (∀ k, TorusHk 0 (h (p k))) →ₗ[ℝ]
    (∀ k, TorusHk (max Mout (K (p k))) (h (p k)))
  model : IsRawMassModel (h := fun k => h (p k)) πp (K ∘ p) Mout ρm C operator
  l2 : (∀ v u, IsEmpty ((F.pathFamily p).Γ v u)) →
    IsRawMassL2 (h := fun k => h (p k)) πp (K ∘ p) Mout (1 + CP * E ^ Pacc) operator
  error : IsRawMassError (h := fun k => h (p k)) πp (K ∘ p) Mout D ν tS tp ρs ρold E Pacc CP
    b (edgeCoefficient (F.pathFamily p) ν e E actual (K ∘ p)) operator

/-- The endpoint corner of the chain core from the first vertex to the last. -/
def ChainCore.corner {F : ChartedFamily ι h D P Ctx} {actual : ∀ a, Ctx a}
    {K : ι → ℕ} {Mout : ℕ} {ν e E tS tp ρs ρold ρm Pacc C CP : ℝ}
    {b : ℝ → Vec 2 → Vec 2} {n : ℕ} {p : Fin (n + 1) → ι} {πp : Fin (n + 1) → ℝ}
    (R : ChainCore F actual K Mout ν e E tS tp ρs ρold ρm Pacc C CP b p πp) :
    TorusHk 0 (h (p 0)) →ₗ[ℝ] TorusHk (max Mout (K (p (Fin.last n)))) (h (p (Fin.last n))) :=
  modelCorner (h := fun k => h (p k)) (K ∘ p) Mout R.operator (Fin.last n) 0

omit [Fintype ι] [DecidableEq ι] in
/-- Mass-weighted core estimates give the exact endpoint corner weight. -/
theorem ChainCore.corner_bound {F : ChartedFamily ι h D P Ctx} {actual : ∀ a, Ctx a}
    {K : ι → ℕ} {Mout : ℕ} {ν e E tS tp ρs ρold ρm Pacc C CP : ℝ}
    {b : ℝ → Vec 2 → Vec 2} {n : ℕ} {p : Fin (n + 1) → ι} {πp : Fin (n + 1) → ℝ}
    (R : ChainCore F actual K Mout ν e E tS tp ρs ρold ρm Pacc C CP b p πp)
    (hπp : ∀ k, 0 < πp k) (hC : 0 ≤ C) (f : TorusHk 0 (h (p 0))) :
    torusHkNorm ρm (le_max_left Mout _) (R.corner f) ≤
      C * Real.sqrt (πp (Fin.last n) / πp 0) * torusHkNorm 1 (le_refl 0) f :=
  modelCorner_bound πp hπp (K ∘ p) Mout ρm C hC R.operator R.model (Fin.last n) 0 f

omit [Fintype ι] [DecidableEq ι] in
/-- An edge-free singleton core supplies its near-contraction without a mass factor. -/
theorem ChainCore.corner_l2 {F : ChartedFamily ι h D P Ctx} {actual : ∀ a, Ctx a}
    {K : ι → ℕ} {Mout : ℕ} {ν e E tS tp ρs ρold ρm Pacc C CP : ℝ}
    {b : ℝ → Vec 2 → Vec 2} {p : Fin 1 → ι} {πp : Fin 1 → ℝ}
    (R : ChainCore F actual K Mout ν e E tS tp ρs ρold ρm Pacc C CP b p πp)
    (hπp : ∀ k, 0 < πp k) (hδ : 0 ≤ 1 + CP * E ^ Pacc) (f : TorusHk 0 (h (p 0))) :
    torusHkNorm 1 (Nat.zero_le _) (R.corner f) ≤
      (1 + CP * E ^ Pacc) * torusHkNorm 1 (le_refl 0) f := by
  have hh := modelCorner_l2 πp hπp (K ∘ p) Mout _ hδ R.operator
    (R.l2 (F.pathFamily_zero_edges p)) (Fin.last 0) 0 f
  have hl : Fin.last 0 = (0 : Fin 1) := Fin.ext rfl
  have hm : πp (Fin.last 0) = πp 0 := congrArg πp hl
  rw [hm, div_self (hπp 0).ne', Real.sqrt_one, mul_one] at hh
  exact hh

omit [Fintype ι] [DecidableEq ι] in
/-- Endpoint physical error of a chain core, with the same operator as its model. -/
theorem ChainCore.corner_error_mass {F : ChartedFamily ι h D P Ctx} {actual : ∀ a, Ctx a}
    {K : ι → ℕ} {Mout : ℕ} {ν e E tS tp ρs ρold ρm Pacc C CP : ℝ}
    {b : ℝ → Vec 2 → Vec 2} {n : ℕ} {p : Fin (n + 1) → ι} {πp : Fin (n + 1) → ℝ}
    (R : ChainCore F actual K Mout ν e E tS tp ρs ρold ρm Pacc C CP b p πp)
    (hπp : ∀ k, 0 < πp k) (f : ∀ k, TorusHk (K (p k)) (h (p k)))
    (Fv : Fin (n + 1) → ℝ)
    (hf : ∀ k, torusHkNorm ρold (le_refl (K (p k))) (f k) ≤ Fv k)
    (u : ∀ k, ℝ → TorusHk (K (p k)) (h (p k)))
    (w : ∀ k, ℝ → TorusHk (K (p k) + 1) (h (p k)))
    (hs : IsCoupledWeakSolutionTorus ν tS tp b D (K ∘ p)
      (edgeCoefficient (F.pathFamily p) ν e E actual (K ∘ p))
      f (fun _ _ => 0) (fun _ _ => 0) u w) :
    torusHkNorm ρs (le_refl (K (p (Fin.last n))))
      (u (Fin.last n) tp - truncateTorusHk (le_max_right Mout _)
        (R.operator (fun k => truncateTorusHk (Nat.zero_le _) (f k)) (Fin.last n))) ≤
      Real.sqrt (πp (Fin.last n)) *
        (CP * E ^ Pacc * Real.sqrt (∑ k, (πp k)⁻¹ * Fv k ^ 2)) := by
  let er : ∀ k, TorusHk (K (p k)) (h (p k)) := fun k =>
    u k tp - truncateTorusHk (le_max_right Mout _) (R.operator
      (fun k => truncateTorusHk (Nat.zero_le _) (f k)) k)
  have hh := R.error f Fv hf u w (hs : _)
  have hc := torus_component_mass_le πp hπp (K ∘ p) ρs er (Fin.last n)
  exact hc.trans (mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _))


omit [Fintype ι] [DecidableEq ι] in
/-- With datum at the first vertex alone, the physical corner error has a single input norm. -/
theorem ChainCore.corner_error_single {F : ChartedFamily ι h D P Ctx} {actual : ∀ a, Ctx a}
    {K : ι → ℕ} {Mout : ℕ} {ν e E tS tp ρs ρold ρm Pacc C CP : ℝ}
    {b : ℝ → Vec 2 → Vec 2} {n : ℕ} {p : Fin (n + 1) → ι} {πp : Fin (n + 1) → ℝ}
    (R : ChainCore F actual K Mout ν e E tS tp ρs ρold ρm Pacc C CP b p πp)
    (hπp : ∀ k, 0 < πp k) (hπ0 : πp 0 = 1)
    (f : TorusHk (K (p 0)) (h (p 0))) (G : ℝ)
    (hf : torusHkNorm ρold (le_refl (K (p 0))) f ≤ G)
    (u : ∀ k, ℝ → TorusHk (K (p k)) (h (p k)))
    (w : ∀ k, ℝ → TorusHk (K (p k) + 1) (h (p k)))
    (hs : IsCoupledWeakSolutionTorus ν tS tp b D (K ∘ p)
      (edgeCoefficient (F.pathFamily p) ν e E actual (K ∘ p))
      (Pi.single 0 f) (fun _ _ => 0) (fun _ _ => 0) u w) :
    torusHkNorm ρs (le_refl (K (p (Fin.last n))))
      (u (Fin.last n) tp - truncateTorusHk (le_max_right Mout _)
        (R.corner (truncateTorusHk (Nat.zero_le _) f))) ≤
      Real.sqrt (πp (Fin.last n)) * (CP * E ^ Pacc * G) := by
  classical
  have hh := R.corner_error_mass hπp (Pi.single 0 f) (Pi.single 0 G)
    (torusSingle_prepared_bound (h := fun k => h (p k)) (K ∘ p) ρold 0 f G hf) u w hs
  have hin := truncateTorusHk_single (h := fun k => h (p k)) (K ∘ p) 0 f
  have hout := congrArg
    (fun z : ∀ k, TorusHk 0 (h (p k)) => R.operator z (Fin.last n)) hin
  have he := congrArg
    (fun z => torusHkNorm ρs (le_refl (K (p (Fin.last n))))
      (u (Fin.last n) tp - truncateTorusHk (le_max_right Mout _) z)) hout
  apply he.symm.trans_le
  apply hh.trans_eq
  have hG : 0 ≤ G := (Real.sqrt_nonneg _).trans hf
  rw [single_scalar_mass πp 0 G, hπ0, inv_one, one_mul, Real.sqrt_sq hG]

local instance pathBlocksPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

section Collection
variable (F : ChartedFamily ι h D P Ctx) (actual : ∀ a, Ctx a)
    (K : ι → ℕ) (Mout H : ℕ) (A : Matrix ι ι ℝ)
    (ν e E tS tp ρs ρold ρm Pacc C CP : ℝ) (b : ℝ → Vec 2 → Vec 2)

/-- The core operators for every retained chain, with common constants and endpoint. -/
def PathCoreCollection := ∀ (n : ℕ) (v : ι) (p : Incoming ι n),
  IncomingValid F A v p → n ≤ H →
    ChainCore F actual K Mout ν e E tS tp ρs ρold ρm Pacc C CP b
      (incomingVertices v p) (pathMass (incomingVertices v p) A)

variable {F actual K Mout H A ν e E tS tp ρs ρold ρm Pacc C CP b}
    (R : PathCoreCollection F actual K Mout H A ν e E tS tp ρs ρold ρm Pacc C CP b)

/-- One retained chain, with its source and endpoint identified in the original family. -/
def validPathCorner {n : ℕ} (v u : ι)
    (p : {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u}) (hn : n ≤ H) :
    TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v) :=
  (torusVertexCast (h := h) (fun i => max Mout (K i)) _ v (incomingVertices_last v p.val)).comp
    ((R n v p.val p.property.1 hn).corner.comp
      (torusVertexCast (h := h) (fun _ => 0) u _
        ((incomingVertices_first v p.val).trans p.property.2).symm))

omit [Fintype ι] [DecidableEq ι] in
/-- A retained corner has precisely its path product as its entrywise norm factor. -/
theorem validPathCorner_bound (hC : 0 ≤ C) {n : ℕ} (v u : ι)
    (p : {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u})
    (hn : n ≤ H) (f : TorusHk 0 (h u)) :
    torusHkNorm ρm (le_max_left Mout (K v)) (validPathCorner R v u p hn f) ≤
      C * incomingWeight A v p.val * torusHkNorm 1 (le_refl 0) f := by
  have hpos := fun k => (incomingVertices_edges F A v p.val p.property.1 k).2
  have hm := pathMass_pos (incomingVertices v p.val) A hpos
  let fin := torusVertexCast (h := h) (fun _ => 0) u _
    ((incomingVertices_first v p.val).trans p.property.2).symm f
  have hh := (R n v p.val p.property.1 hn).corner_bound hm hC fin
  rw [pathMass_first (incomingVertices v p.val) A, div_one,
    pathMass_last_sqrt (incomingVertices v p.val) A hpos, pathProduct_incomingVertices A v p.val] at hh
  change torusHkNorm ρm (le_max_left Mout (K v))
    (torusVertexCast (h := h) (fun i => max Mout (K i)) _ v (incomingVertices_last v p.val)
      ((R n v p.val p.property.1 hn).corner fin)) ≤ _
  rw [torusVertexCast_order_norm (fun i => max Mout (K i)) Mout (fun i => le_max_left Mout (K i))]
  have hf : torusHkNorm 1 (le_refl 0) fin = torusHkNorm 1 (le_refl 0) f :=
    torusVertexCast_norm (fun _ => 0) _ _ _ 1 f
  rw [hf] at hh
  exact hh

/-- The positive-length block is the sum of retained source-path corners. -/
def pathSourceBlock (n : ℕ) (v u : ι) :
    TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v) :=
  if hn : n ≤ H then
    ∑ p : {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u},
      validPathCorner R v u p hn
  else 0

/-- Without an actual edge path, the corresponding block sum is empty. -/
theorem pathSourceBlock_support (n : ℕ) (v u : ι) (hpath : ¬ HasEdgePath F n u v) :
    pathSourceBlock R n v u = 0 := by
  classical
  unfold pathSourceBlock
  split
  · let : IsEmpty {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u} :=
      ⟨fun p => hpath (p.property.2 ▸ incomingValid_hasEdgePath F A v p.val p.property.1)⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
  · rfl

/-- Summed corner estimates give the required positive matrix-power bound. -/
theorem pathSourceBlock_bound (hC : 0 ≤ C) (hA : ∀ v u, 0 ≤ A v u)
    (n : ℕ) (v u : ι) (f : TorusHk 0 (h u)) :
    torusHkNorm ρm (le_max_left Mout (K v)) (pathSourceBlock R n v u f) ≤
      C * (A ^ n) v u * torusHkNorm 1 (le_refl 0) f := by
  classical
  unfold pathSourceBlock
  split
  · rename_i hn
    rw [LinearMap.sum_apply]
    apply (CycleComparison.Reconstruction.torusHkNorm_sum_le ρm (le_max_left Mout (K v)) Finset.univ _).trans
    calc
      (∑ p, torusHkNorm ρm (le_max_left Mout (K v)) (validPathCorner R v u p hn f)) ≤
          ∑ p : {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u},
            C * incomingWeight A v p.val * torusHkNorm 1 (le_refl 0) f :=
        Finset.sum_le_sum (fun p _ => validPathCorner_bound R hC v u p hn f)
      _ = C * (∑ p : {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u},
            incomingWeight A v p.val) * torusHkNorm 1 (le_refl 0) f := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (incomingValid_weight_sum_le F A hA n v u) hC)
        (Real.sqrt_nonneg _)
  · simp only [LinearMap.zero_apply, CycleComparison.Reconstruction.torusHkNorm_zero]
    exact mul_nonneg (mul_nonneg hC (positiveMatrix_pow_nonneg A hA n v u))
      (Real.sqrt_nonneg _)

/-- Endpoint response of a retained path to the original family datum. -/
def retainedPathResponse {n : ℕ} (v : ι) (p : Incoming ι n)
    (hp : IncomingValid F A v p) (hn : n ≤ H) (f : ∀ i, TorusHk 0 (h i)) :
    TorusHk (max Mout (K v)) (h v) :=
  torusVertexCast (h := h) (fun i => max Mout (K i)) _ v (incomingVertices_last v p)
    ((R n v p hp hn).corner (f (incomingVertices v p 0)))

/-- Nonretained paths contribute zero to the path model. -/
def pathResponse {n : ℕ} (v : ι) (p : Incoming ι n) (hn : n ≤ H)
    (f : ∀ i, TorusHk 0 (h i)) : TorusHk (max Mout (K v)) (h v) :=
  if hp : IncomingValid F A v p then retainedPathResponse R v p hp hn f else 0

omit [Fintype ι] [DecidableEq ι] in
/-- A source fibre's corner applied to a family section is its retained path response. -/
theorem validPathCorner_apply_family {n : ℕ} (v u : ι)
    (p : {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u})
    (hn : n ≤ H) (f : ∀ i, TorusHk 0 (h i)) :
    validPathCorner R v u p hn (f u) = retainedPathResponse R v p.val p.property.1 hn f := by
  change torusVertexCast (h := h) (fun i => max Mout (K i)) _ v (incomingVertices_last v p.val)
    ((R n v p.val p.property.1 hn).corner
      (torusVertexCast (h := h) (fun _ => 0) u _
        ((incomingVertices_first v p.val).trans p.property.2).symm (f u))) = _
  rw [torusVertexCast_apply_family]
  rfl

/-- Summing the source blocks recovers the responses of all retained paths of that length. -/
theorem pathSourceBlock_sum (n : ℕ) (hn : n ≤ H) (v : ι) (f : ∀ i, TorusHk 0 (h i)) :
    (∑ u, pathSourceBlock R n v u (f u)) = ∑ p : Incoming ι n, pathResponse R v p hn f := by
  classical
  simp only [pathSourceBlock, dite_eq_left hn, LinearMap.sum_apply]
  calc
    (∑ u, ∑ p : {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u},
      validPathCorner R v u p hn (f u)) =
      ∑ u, ∑ p : {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u},
        retainedPathResponse R v p.val p.property.1 hn f :=
      Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl
        (fun p _ => validPathCorner_apply_family R v u p hn f))
    _ = ∑ p : {p : Incoming ι n // IncomingValid F A v p},
        retainedPathResponse R v p.val p.property hn f :=
      incomingSource_sum F A n v (fun p => retainedPathResponse R v p.val p.property hn f)
    _ = ∑ p : Incoming ι n, pathResponse R v p hn f := by
      symm
      exact Finset.sum_congr_set {p | IncomingValid F A v p} _ _
        (fun p hp => dite_eq_left hp) (fun p hp => dite_eq_right hp)

/-- A response is extended by zero beyond the retained depth. -/
def truncatedPathResponse {n : ℕ} (v : ι) (p : Incoming ι n) (f : ∀ i, TorusHk 0 (h i)) :
    TorusHk (max Mout (K v)) (h v) :=
  if hn : n ≤ H then pathResponse R v p hn f else 0

/-- Grouping by source is valid also beyond the retained depth, where both sides vanish. -/
theorem pathSourceBlock_sum_all (n : ℕ) (v : ι) (f : ∀ i, TorusHk 0 (h i)) :
    (∑ u, pathSourceBlock R n v u (f u)) =
      ∑ p : Incoming ι n, truncatedPathResponse R v p f := by
  classical
  by_cases hn : n ≤ H
  · simpa only [truncatedPathResponse, dite_eq_left hn] using pathSourceBlock_sum R n hn v f
  · simp only [pathSourceBlock, truncatedPathResponse, dite_eq_right hn,
      LinearMap.zero_apply, Finset.sum_const_zero]

/-- The diagonal is the corner of the trivial path. -/
def pathDiagonalBlock (v : ι) : TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v) :=
  validPathCorner R v v (n := 0) ⟨PUnit.unit, ⟨trivial, rfl⟩⟩ (Nat.zero_le H)

omit [Fintype ι] [DecidableEq ι] in
/-- The trivial path has no product loss in its jet estimate. -/
theorem pathDiagonalBlock_bound (hC : 0 ≤ C) (v : ι) (f : TorusHk 0 (h v)) :
    torusHkNorm ρm (le_max_left Mout (K v)) (pathDiagonalBlock R v f) ≤
      C * torusHkNorm 1 (le_refl 0) f := by
  have hh := validPathCorner_bound R hC v v (n := 0) ⟨PUnit.unit, ⟨trivial, rfl⟩⟩
    (Nat.zero_le H) f
  simpa only [pathDiagonalBlock, incomingWeight, mul_one] using hh

omit [Fintype ι] [DecidableEq ι] in
/-- The edge-free trivial chain supplies the diagonal near-contraction. -/
theorem pathDiagonalBlock_l2 (hδ : 0 ≤ 1 + CP * E ^ Pacc) (v : ι) (f : TorusHk 0 (h v)) :
    torusHkNorm 1 (Nat.zero_le _) (pathDiagonalBlock R v f) ≤
      (1 + CP * E ^ Pacc) * torusHkNorm 1 (le_refl 0) f := by
  let core := R 0 v PUnit.unit trivial (Nat.zero_le H)
  have hh := core.corner_l2
    (pathMass_pos (incomingVertices (n := 0) v PUnit.unit) A (fun k => Fin.elim0 k)) hδ f
  change torusHkNorm 1 (Nat.zero_le _) (torusVertexCast (h := h)
    (fun i => max Mout (K i)) v v rfl (core.corner f)) ≤ _
  exact (torusVertexCast_order_norm (fun i => max Mout (K i)) 0
    (fun _ => Nat.zero_le _) v v rfl 1 (core.corner f)).trans_le hh

omit [DecidableEq ι] in
/-- The length-zero model response is exactly the diagonal corner. -/
theorem truncatedPathResponse_zero_sum (v : ι) (f : ∀ i, TorusHk 0 (h i)) :
    (∑ p : Incoming ι 0, truncatedPathResponse R v p f) = pathDiagonalBlock R v (f v) := by
  change (∑ p : PUnit, truncatedPathResponse (n := 0) R v p f) = _
  rw [Fintype.sum_unique]
  unfold truncatedPathResponse
  rw [dite_eq_left (Nat.zero_le H)]
  unfold pathResponse
  rw [dite_eq_left (show IncomingValid F A v (n := 0) PUnit.unit from trivial)]
  rfl

/-- The joint operator is exactly the finite path-response sum. -/
theorem pathBlocks_jointOperator (v : ι) (f : ∀ i, TorusHk 0 (h i)) :
    jointOperator K Mout H (pathDiagonalBlock R) (pathSourceBlock R) f v =
      ∑ n ∈ Finset.range (H + 1), ∑ p : Incoming ι n, truncatedPathResponse R v p f := by
  classical
  have hset : Finset.range (H + 1) = insert 0 (Finset.Icc 1 H) := by
    rw [Nat.range_succ_eq_Icc_zero]
    exact (Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le H)).symm
  rw [hset,
    Finset.sum_insert (show 0 ∉ Finset.Icc 1 H by simp only [Finset.mem_Icc]; omega),
    truncatedPathResponse_zero_sum]
  unfold jointOperator
  apply congrArg (pathDiagonalBlock R v (f v) + ·)
  exact Finset.sum_congr rfl (fun n _ => pathSourceBlock_sum_all R n v f)

/-- All four raw triangular clauses follow from the path-core collection. -/
theorem pathBlocks_model (hC : 0 ≤ C) (hA : ∀ v u, 0 ≤ A v u)
    (hδ : 0 ≤ 1 + CP * E ^ Pacc) :
    IsRawTriangularModel K Mout H F A E Pacc ρm C CP
      (pathDiagonalBlock R) (pathSourceBlock R) :=
  ⟨fun n _ _ v u hh => pathSourceBlock_support R n v u hh,
    pathDiagonalBlock_l2 R hδ, pathDiagonalBlock_bound R hC,
    fun n _ _ v u f => pathSourceBlock_bound R hC hA n v u f⟩

end Collection
section Choice
variable (F : ChartedFamily ι h D P Ctx) (actual : ∀ a, Ctx a)
    (K : ι → ℕ) (Mout H : ℕ) (A : Matrix ι ι ℝ)
    (ν e E tS tp ρs ρold ρm Pacc C CP : ℝ) (b : ℝ → Vec 2 → Vec 2)

/-- The clauses of a chain core for an operator on the path family of a backward path (they
mention the path masses and the path matrix only, not the masses of the family). -/
def ChainCoreProp {n : ℕ} (v : ι) (p : Incoming ι n)
    (T : (∀ k, TorusHk 0 (h (incomingVertices v p k))) →ₗ[ℝ]
      (∀ k, TorusHk (max Mout (K (incomingVertices v p k))) (h (incomingVertices v p k)))) :
    Prop :=
  IsRawMassModel (h := fun k => h (incomingVertices v p k)) (pathMass (incomingVertices v p) A)
      (K ∘ incomingVertices v p) Mout ρm C T ∧
    ((∀ v' u', IsEmpty ((F.pathFamily (incomingVertices v p)).Γ v' u')) →
      IsRawMassL2 (h := fun k => h (incomingVertices v p k)) (pathMass (incomingVertices v p) A)
        (K ∘ incomingVertices v p) Mout (1 + CP * E ^ Pacc) T) ∧
    IsRawMassError (h := fun k => h (incomingVertices v p k)) (pathMass (incomingVertices v p) A)
      (K ∘ incomingVertices v p) Mout D ν tS tp ρs ρold E Pacc CP b
      (edgeCoefficient (F.pathFamily (incomingVertices v p)) ν e E actual (K ∘ incomingVertices v p))
      T

/-- **The chosen core operator** of a backward path: an operator with the chain-core clauses when
one exists (`Classical.epsilon`). It is defined before any mass family of the original family. -/
def chainCoreChoice {n : ℕ} (v : ι) (p : Incoming ι n) :
    (∀ k, TorusHk 0 (h (incomingVertices v p k))) →ₗ[ℝ]
      (∀ k, TorusHk (max Mout (K (incomingVertices v p k))) (h (incomingVertices v p k))) :=
  Classical.epsilon (ChainCoreProp F actual K Mout A ν e E tS tp ρs ρold ρm Pacc C CP b v p)

/-- The chain core of the chosen operator, once some operator has the clauses. -/
def chainCoreOfChoice {n : ℕ} (v : ι) (p : Incoming ι n)
    (hex : ∃ T, ChainCoreProp F actual K Mout A ν e E tS tp ρs ρold ρm Pacc C CP b v p T) :
    ChainCore F actual K Mout ν e E tS tp ρs ρold ρm Pacc C CP b (incomingVertices v p)
      (pathMass (incomingVertices v p) A) where
  operator := chainCoreChoice F actual K Mout A ν e E tS tp ρs ρold ρm Pacc C CP b v p
  model := (Classical.epsilon_spec hex).1
  l2 := (Classical.epsilon_spec hex).2.1
  error := (Classical.epsilon_spec hex).2.2

/-- The core collection of the chosen operators. -/
def chosenCollection
    (hex : ∀ (n : ℕ) (v : ι) (p : Incoming ι n), IncomingValid F A v p → n ≤ H →
      ∃ T, ChainCoreProp F actual K Mout A ν e E tS tp ρs ρold ρm Pacc C CP b v p T) :
    PathCoreCollection F actual K Mout H A ν e E tS tp ρs ρold ρm Pacc C CP b :=
  fun n v p hp hn => chainCoreOfChoice F actual K Mout A ν e E tS tp ρs ρold ρm Pacc C CP b v p
    (hex n v p hp hn)

/-- The retained corner of the chosen operator. -/
def chosenPathCorner {n : ℕ} (v u : ι)
    (p : {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u}) :
    TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v) :=
  (torusVertexCast (h := h) (fun i => max Mout (K i)) _ v (incomingVertices_last v p.val)).comp
    ((modelCorner (h := fun k => h (incomingVertices v p.val k)) (K ∘ incomingVertices v p.val)
        Mout (chainCoreChoice F actual K Mout A ν e E tS tp ρs ρold ρm Pacc C CP b v p.val)
        (Fin.last n) 0).comp
      (torusVertexCast (h := h) (fun _ => 0) u _
        ((incomingVertices_first v p.val).trans p.property.2).symm))

/-- **The source blocks of the chosen operators** (mass-free). -/
def chosenSourceBlock (n : ℕ) (v u : ι) :
    TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v) :=
  if n ≤ H then
    ∑ p : {p : Incoming ι n // IncomingValid F A v p ∧ incomingSource v p = u},
      chosenPathCorner F actual K Mout A ν e E tS tp ρs ρold ρm Pacc C CP b v u p
  else 0

/-- **The diagonal block of the chosen operators** (mass-free). -/
def chosenDiagonalBlock (v : ι) : TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v) :=
  chosenPathCorner F actual K Mout A ν e E tS tp ρs ρold ρm Pacc C CP b v v (n := 0)
    ⟨PUnit.unit, ⟨trivial, rfl⟩⟩

/-- The source blocks of the chosen collection are the chosen source blocks. -/
theorem pathSourceBlock_chosen
    (hex : ∀ (n : ℕ) (v : ι) (p : Incoming ι n), IncomingValid F A v p → n ≤ H →
      ∃ T, ChainCoreProp F actual K Mout A ν e E tS tp ρs ρold ρm Pacc C CP b v p T) :
    pathSourceBlock (chosenCollection F actual K Mout H A ν e E tS tp ρs ρold ρm Pacc C CP b hex) =
      chosenSourceBlock F actual K Mout H A ν e E tS tp ρs ρold ρm Pacc C CP b := by
  funext n v u
  unfold pathSourceBlock chosenSourceBlock
  split_ifs <;> rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The diagonal block of the chosen collection is the chosen diagonal block. -/
theorem pathDiagonalBlock_chosen
    (hex : ∀ (n : ℕ) (v : ι) (p : Incoming ι n), IncomingValid F A v p → n ≤ H →
      ∃ T, ChainCoreProp F actual K Mout A ν e E tS tp ρs ρold ρm Pacc C CP b v p T) :
    pathDiagonalBlock (chosenCollection F actual K Mout H A ν e E tS tp ρs ρold ρm Pacc C CP b hex) =
      chosenDiagonalBlock F actual K Mout A ν e E tS tp ρs ρold ρm Pacc C CP b :=
  rfl

end Choice
end

end AVRegularity.CycleJointProofs.PathReduction
end
