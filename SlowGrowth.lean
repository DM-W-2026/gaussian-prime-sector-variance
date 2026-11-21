import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite resonance and the last real-variable implication in the
Gaussian-sector slow-growth argument. Reproduce in a mathlib checkout at
c44e0c8ee63ca166450922a373c7409c5d26b00b with Lean 4.19.0:
  lake env lean /path/to/SlowGrowth.lean
The analytic energy and projection estimates are explicit hypotheses. -/
namespace GaussianSector

noncomputable def cell (x : ℝ) : Fin 12 :=
  ⟨⌊12 * Int.fract x⌋₊, (Nat.floor_lt (mul_nonneg (by norm_num) (Int.fract_nonneg x))).2 (by
    push_cast
    linarith [Int.fract_lt_one x])⟩

private theorem cell_close {x y : ℝ} (h : cell x = cell y) :
    |Int.fract x - Int.fract y| < 1 / 12 := by
  have he : ⌊12 * Int.fract x⌋₊ = ⌊12 * Int.fract y⌋₊ := congrArg Fin.val h
  have he' := congrArg (fun n : ℕ => (n : ℝ)) he
  have hx := Nat.floor_le (show 0 ≤ 12 * Int.fract x by exact mul_nonneg (by norm_num) (Int.fract_nonneg _))
  have hy := Nat.floor_le (show 0 ≤ 12 * Int.fract y by exact mul_nonneg (by norm_num) (Int.fract_nonneg _))
  have hx' := Nat.lt_floor_add_one (12 * Int.fract x)
  have hy' := Nat.lt_floor_add_one (12 * Int.fract y)
  apply abs_lt.mpr
  constructor <;> linarith

/-- One multiplier aligns all d ordinates, with an explicit size bound.
For the paper specialize a i to y₀ γᵢ / (2π). -/
theorem simultaneous_alignment {d : ℕ} (a : Fin d → ℝ) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ 12 ^ d ∧
      ∀ i, ∃ z : ℤ, |(q : ℝ) * a i - z| < 1 / 12 := by
  classical
  let bins (j : Fin (12 ^ d + 1)) (i : Fin d) := cell ((j.val : ℝ) * a i)
  obtain ⟨u, v, huv, he⟩ := Fintype.exists_ne_map_eq_of_card_lt bins (by simp)
  have step (l r : Fin (12 ^ d + 1)) (hlt : l.val < r.val)
      (heq : bins l = bins r) :
      ∃ q : ℕ, 1 ≤ q ∧ q ≤ 12 ^ d ∧
        ∀ i, ∃ z : ℤ, |(q : ℝ) * a i - z| < 1 / 12 := by
    refine ⟨r.val - l.val, by omega, by have := r.isLt; omega, ?_⟩
    intro i
    refine ⟨⌊(r.val : ℝ) * a i⌋ - ⌊(l.val : ℝ) * a i⌋, ?_⟩
    have hclose := cell_close (congrFun heq.symm i)
    rw [Nat.cast_sub (Nat.le_of_lt hlt), Int.cast_sub]
    convert hclose using 2
    unfold Int.fract
    ring
  rcases lt_or_gt_of_ne huv with h | h
  · exact step u v h he
  · exact step v u h he.symm

/-- Finite summation-by-parts form of common-radius extraction.
The weights w are signed changes of the smooth cutoff; v i j is the
sharp partial sum in mode i at radius j. The witness j serves every mode. -/
theorem common_radius {ι κ : Type*} (modes : Finset ι) (radii : Finset κ)
    (hr : radii.Nonempty) (w : κ → ℝ) (v : ι → κ → ℝ) :
    ∃ r ∈ radii,
      (∑ j ∈ radii, w j * ∑ i ∈ modes, v i j)^2 ≤
        (∑ j ∈ radii, |w j|)^2 * (modes.card : ℝ) * ∑ i ∈ modes, (v i r)^2 := by
  classical
  let block (j : κ) := ∑ i ∈ modes, v i j
  obtain ⟨r, hr', hmax⟩ := radii.exists_max_image (fun j => |block j|) hr
  refine ⟨r, hr', ?_⟩
  have bound : |∑ j ∈ radii, w j * block j| ≤ (∑ j ∈ radii, |w j|) * |block r| := by
    calc
      _ ≤ ∑ j ∈ radii, |w j * block j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ radii, |w j| * |block r| := Finset.sum_le_sum fun j hj => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hmax j hj) (abs_nonneg _)
      _ = _ := (Finset.sum_mul ..).symm
  have cs : (block r)^2 ≤ (modes.card : ℝ) * ∑ i ∈ modes, (v i r)^2 := by
    simpa [block] using Finset.sum_mul_sq_le_sq_mul_sq modes (fun _ => (1 : ℝ)) (fun i => v i r)
  have sqbound := pow_le_pow_left₀ (abs_nonneg _) bound 2
  rw [sq_abs, mul_pow, sq_abs] at sqbound
  exact (sqbound.trans (mul_le_mul_of_nonneg_left cs (sq_nonneg _))).trans_eq (by ring)

/-- Explicit lower bound for V/P after selecting a common sharp radius.
E is its block energy, A the scale x/(log x)^2, L = log M.
The three estimates and the comparison of K and M are inputs. -/
theorem ratio_from_block {E V P A M L K B C : ℝ}
    (hP : 0 < P) (hK : 0 < K) (hL : 0 ≤ L)
    (hB : 0 < B) (hC : 0 < C)
    (energy : A * M * L^2 ≤ E) (projection : E ≤ V * K^2)
    (prediction : P * K ≤ B * A * L) (scale : K ≤ C * M) (hA : 0 ≤ A) :
    L / (B * C) ≤ V / P := by
  have t1 := mul_le_mul_of_nonneg_right prediction (mul_nonneg hL hK.le)
  have t2 := mul_le_mul_of_nonneg_left scale (show 0 ≤ B * A * L^2 by positivity)
  have t3 := mul_le_mul_of_nonneg_left (energy.trans projection)
    (show 0 ≤ B * C by positivity)
  apply (div_le_div_iff₀ (mul_pos hB hC) hP).2
  apply le_of_mul_le_mul_right (a := K^2) _ (sq_pos_of_pos hK)
  nlinarith only [t1, t2, t3]

noncomputable def slowK (x : ℝ) : ℕ :=
  ⌊Real.log (Real.log x) / Real.log (Real.log (Real.log x))⌋₊

noncomputable def predicted (N : ℝ) (K : ℕ) : ℝ :=
  N / K * min 1 (2 * Real.log K / Real.log N)

/-- A cofinal supply of lower bounds on the original ratio excludes a limit of one.
The paper supplies these lower bounds for its specific N and V. -/
theorem excludes_pointwise_prediction (N : ℝ → ℝ) (V : ℝ → ℕ → ℝ)
    (large : ∀ T : ℝ, ∃ x ≥ T, 2 ≤ V x (slowK x) / predicted (N x) (slowK x)) :
    ¬ Filter.Tendsto (fun x => V x (slowK x) / predicted (N x) (slowK x))
      Filter.atTop (nhds 1) := by
  intro h
  have ev := h.eventually (gt_mem_nhds (show (1 : ℝ) < 2 by norm_num))
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 ev
  obtain ⟨x, hx, hlarge⟩ := large T
  exact (not_lt_of_ge hlarge) (hT x hx)

/-- Assemble the on-line branch at the prescribed slow width. Inputs are
the common-radius energy, arc projection, PNT prediction comparison and
parameter selection, with constants already absorbed into E and A.
The radius and L must be simultaneously large. -/
theorem counterexample_of_blocks (N : ℝ → ℝ) (V : ℝ → ℕ → ℝ)
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (blocks : ∀ T U : ℝ, ∃ x ≥ T, ∃ E A M L : ℝ,
      U ≤ L ∧ 0 ≤ L ∧ 0 ≤ A ∧ 0 < (slowK x : ℝ) ∧
      0 < predicted (N x) (slowK x) ∧
      A * M * L^2 ≤ E ∧ E ≤ V x (slowK x) * (slowK x : ℝ)^2 ∧
      predicted (N x) (slowK x) * (slowK x : ℝ) ≤ B * A * L ∧
      (slowK x : ℝ) ≤ C * M) :
    ∀ T R : ℝ, ∃ x ≥ T, R ≤ V x (slowK x) / predicted (N x) (slowK x) := by
  intro T R
  obtain ⟨x, hx, E, A, M, L, hU, hL, hA, hK, hP, he, hv, hp, hk⟩ :=
    blocks T (R * (B * C))
  exact ⟨x, hx, ((le_div_iff₀ (mul_pos hB hC)).2 hU).trans
    (ratio_from_block hP hK hL hB hC he hv hp hk hA)⟩

end GaussianSector

#print axioms GaussianSector.simultaneous_alignment
#print axioms GaussianSector.common_radius
#print axioms GaussianSector.ratio_from_block
#print axioms GaussianSector.excludes_pointwise_prediction

#print axioms GaussianSector.counterexample_of_blocks
