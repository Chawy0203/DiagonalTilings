import Init

/-!
# The all-diagonal tiling of an even rectangle

Dawid Ryłko's OEIS entry A401673, https://oeis.org/A401673, conjectures
in particular that T(n, n²) = 1. This file proves that equality by proving
existence and uniqueness on every (2h) × (2w) rectangle.

A tiling is represented by the function taking each cell to its partner.
The partners are diagonal neighbors and applying the function twice
returns the starting cell. Two pairs may cross inside a 2 × 2 block.

Check with `lean DiagonalTilings.lean`. Only the Lean standard library is
required. The theorem for squares is `DiagonalTilings.square_unique`.
-/

namespace DiagonalTilings

abbrev Cell (h w : Nat) := Fin (2 * h) × Fin (2 * w)

/-- Two coordinates differ by exactly one. -/
def Adjacent (x y : Nat) : Prop := x + 1 = y ∨ y + 1 = x

def IsDiagonalTiling {h w : Nat} (mate : Cell h w → Cell h w) : Prop :=
  (∀ p, mate (mate p) = p) ∧
  (∀ p, Adjacent p.1.val (mate p).1.val ∧ Adjacent p.2.val (mate p).2.val)

/-- Exchange 0 with 1, 2 with 3, and so on. -/
private def flipIndex (x : Nat) : Nat :=
  if x % 2 = 0 then x + 1 else x - 1

private theorem flip_lt {x n : Nat} (hx : x < 2 * n) : flipIndex x < 2 * n := by
  unfold flipIndex
  split <;> omega

private theorem flip_twice (x : Nat) : flipIndex (flipIndex x) = x := by
  by_cases even : x % 2 = 0
  · have odd : (x + 1) % 2 ≠ 0 := by omega
    simp [flipIndex, even, odd]
  · have prevEven : (x - 1) % 2 = 0 := by omega
    simp [flipIndex, even, prevEven] <;> omega

private theorem flip_adjacent (x : Nat) : Adjacent x (flipIndex x) := by
  unfold Adjacent flipIndex
  split <;> omega

private def flipCoord {n : Nat} (x : Fin (2 * n)) : Fin (2 * n) :=
  ⟨flipIndex x.val, flip_lt x.isLt⟩

/-- The two crossing diagonals in each disjoint 2 × 2 block. -/
def canonical {h w : Nat} (p : Cell h w) : Cell h w :=
  (flipCoord p.1, flipCoord p.2)

private theorem canonical_twice {h w : Nat} (p : Cell h w) :
    canonical (canonical p) = p :=
  Prod.ext (Fin.ext (flip_twice p.1.val)) (Fin.ext (flip_twice p.2.val))

theorem canonical_is_tiling (h w : Nat) :
    IsDiagonalTiling (canonical (h := h) (w := w)) :=
  ⟨canonical_twice, fun p => ⟨flip_adjacent p.1.val, flip_adjacent p.2.val⟩⟩

/-- Count even coordinates from the near boundary and odd ones from the far boundary. -/
private def axisRank (n x : Nat) : Nat :=
  if x % 2 = 0 then x else 2 * n - 1 - x

/-- Follow one adjacent step and then flip. On each axis this either
fixes the coordinate or strictly decreases its rank. -/
private theorem axis_step {n x y : Nat} (hx : x < 2 * n) (hy : y < 2 * n)
    (hxy : Adjacent x y) :
    axisRank n (flipIndex y) ≤ axisRank n x ∧
    (axisRank n (flipIndex y) = axisRank n x → flipIndex y = x) := by
  unfold Adjacent at hxy
  by_cases even : x % 2 = 0
  · have odd : y % 2 ≠ 0 := by omega
    have prevEven : (y - 1) % 2 = 0 := by omega
    simp [axisRank, flipIndex, even, odd, prevEven] <;> omega
  · have evenY : y % 2 = 0 := by omega
    have nextOdd : (y + 1) % 2 ≠ 0 := by omega
    simp [axisRank, flipIndex, even, evenY, nextOdd] <;> omega

/-- An injective map that would decrease rank at every moved point is the identity. -/
private theorem fixed_of_descent {α : Type} (f : α → α) (rank : α → Nat)
    (injective : ∀ {x y}, f x = f y → x = y)
    (descent : ∀ x, f x ≠ x → rank (f x) < rank x) (x : α) : f x = x := by
  suffices all : ∀ k, ∀ y, rank y < k → f y = y from
    all (rank x + 1) x (Nat.lt_succ_self _)
  intro k
  induction k with
  | zero =>
    intro y hy
    omega
  | succ k ih =>
    intro y hy
    by_cases eq : f y = y
    · exact eq
    · have lt := descent y eq
      exact injective (ih (f y) (by omega))

theorem tiling_eq_canonical {h w : Nat} {mate : Cell h w → Cell h w}
    (tiling : IsDiagonalTiling mate) : mate = canonical := by
  let f (p : Cell h w) := canonical (mate p)
  let rank (p : Cell h w) := axisRank h p.1.val + axisRank w p.2.val
  have injective : ∀ {p q : Cell h w}, f p = f q → p = q := by
    intro p q eq
    have same := congrArg (fun v : Cell h w => mate (canonical v)) eq
    simpa only [f, canonical_twice, tiling.1] using same
  have descent (p : Cell h w) (moved : f p ≠ p) : rank (f p) < rank p := by
    obtain ⟨rowStep, colStep⟩ := tiling.2 p
    obtain ⟨rowLe, rowEq⟩ := axis_step p.1.isLt (mate p).1.isLt rowStep
    obtain ⟨colLe, colEq⟩ := axis_step p.2.isLt (mate p).2.isLt colStep
    change axisRank h (flipIndex (mate p).1.val) + axisRank w (flipIndex (mate p).2.val)
      < axisRank h p.1.val + axisRank w p.2.val
    apply Nat.lt_of_not_ge
    intro bad
    apply moved
    exact Prod.ext (Fin.ext (rowEq (by omega))) (Fin.ext (colEq (by omega)))
  funext p
  have fixed := fixed_of_descent f rank injective descent p
  have same := congrArg (fun v : Cell h w => canonical v) fixed
  simpa only [f, canonical_twice] using same

/-- Existence and uniqueness on every even-by-even rectangle, including empty boards. -/
theorem rectangle_unique (h w : Nat) :
    ∃ mate : Cell h w → Cell h w,
      IsDiagonalTiling mate ∧ ∀ other, IsDiagonalTiling other → other = mate :=
  ⟨canonical, canonical_is_tiling h w, fun _ valid => tiling_eq_canonical valid⟩

/-- The all-diagonal coefficient T(n, n²) of OEIS A401673 is one. -/
theorem square_unique (n : Nat) :
    ∃ mate : Cell n n → Cell n n,
      IsDiagonalTiling mate ∧ ∀ other, IsDiagonalTiling other → other = mate :=
  rectangle_unique n n

#check square_unique

end DiagonalTilings
