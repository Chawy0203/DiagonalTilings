# DiagonalTilings

Every rectangle with an even number of rows and an even number of columns has exactly one tiling by diagonal pairs. Each cell must be paired with a cell one row and one column away. Pairs may cross. The Lean 4 formalization includes empty rectangles.

On a 2 × 2 board, equal letters mark paired cells. Repeating this block across the board gives the unique tiling.

```text
A B
B A
```

## Check the proof

With Lean 4 installed, run the following from the repository root. The proof imports only `Init` and needs no external packages.

```sh
lean DiagonalTilings.lean
```

The final `#check` prints the type of `DiagonalTilings.square_unique`. A successful check exits with status zero.

## Why the tiling is unique

The canonical partner swaps adjacent row indices (0 with 1, 2 with 3, and so on) and does the same for column indices. Applying both swaps twice returns to the original cell, so this rule gives a valid tiling.

Now start at any cell, follow its partner in a proposed tiling, then follow the canonical partner. This two-step map is injective because each partner map is its own inverse. The proof assigns a rank to each coordinate by measuring even indices from the near edge and odd indices from the far edge. Neither coordinate rank can increase during the two steps, and a changed coordinate strictly decreases in rank.

If any cell moved, choose a moved cell of least total rank. Its image would have smaller rank and would therefore be fixed. The moved cell and its image would then map to the same cell, contradicting injectivity. Thus the two steps always return to the starting cell, and the proposed tiling agrees everywhere with the canonical one.

## Main results

| Theorem in `DiagonalTilings` | Statement |
| --- | --- |
| `canonical_is_tiling` | The repeated 2 × 2 construction pairs every cell with a diagonal neighbor. |
| `tiling_eq_canonical` | Every valid partner map equals the canonical one. |
| `rectangle_unique` | A unique tiling exists on every (2h) × (2w) rectangle. |
| `square_unique` | Setting h = w gives the result for every even-sided square. |

The square theorem is the partner-map formulation of the all-diagonal case described as T(n, n²) = 1 in the source file. The counting problem comes from Dawid Ryłko’s [OEIS entry A401673](https://oeis.org/A401673).

## Credits

Chawy0203 and ChatGPT worked together to develop this proof and its Lean formalization.
