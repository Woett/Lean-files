/-
Read my comment here for some context: https://www.erdosproblems.com/forum/thread/231#post-4294

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
We define the four-letter alphabet Alphabet = {a, b, c, d} and the cyclic permutation sigma. We then define Keränen's morphism g. g(a) is given explicitly, and g(b), g(c), g(d) are obtained by applying sigma cyclically.
-/
inductive Alphabet
| a | b | c | d
deriving DecidableEq

open Alphabet

def sigma_perm : Alphabet → Alphabet
| a => b
| b => c
| c => d
| d => a

def charToAlphabet (char : Char) : Alphabet :=
  match char with
  | 'a' => a
  | 'b' => b
  | 'c' => c
  | 'd' => d
  | _ => a

def stringToAlphabet (s : String) : List Alphabet :=
  s.toList.map charToAlphabet

def g_a_str := "abcacdcbcdcadcdbdabacabadbabcbdbcbacbcdcacbabdabacadcbcdcacdbcbacbcdcacdcbdcdadbdcbca"

def g_a : List Alphabet := stringToAlphabet g_a_str

def g : Alphabet → List Alphabet
| a => g_a
| b => g_a.map sigma_perm
| c => g_a.map (sigma_perm ∘ sigma_perm)
| d => g_a.map (sigma_perm ∘ sigma_perm ∘ sigma_perm)

/-
Optimized computational verification functions.
-/
def count_v2 (l : List Alphabet) (x : Alphabet) : Nat :=
  l.foldl (fun n y => if x == y then n + 1 else n) 0

def isPerm_v2 (u v : List Alphabet) : Bool :=
  count_v2 u a == count_v2 v a &&
  count_v2 u b == count_v2 v b &&
  count_v2 u c == count_v2 v c &&
  count_v2 u d == count_v2 v d

def isSquareFreeSuffixBoundary (w : List Alphabet) (added_len : Nat) : Bool :=
  let min_k := added_len / 2 + 1
  let max_k := w.length / 2
  if min_k > max_k then true
  else
    (List.range (max_k - min_k + 1)).all (fun i =>
      let k := min_k + i
      let u := (w.drop (w.length - 2 * k)).take k
      let v := w.drop (w.length - k)
      not (isPerm_v2 u v))

def check_prefixes_g_optimized (current_g : List Alphabet) (next_g : List Alphabet) : Bool :=
  (List.range next_g.length).all (fun i =>
    let p := next_g.take (i + 1)
    isSquareFreeSuffixBoundary (current_g ++ p) p.length)

def dfs_check_optimized (w : List Alphabet) (g_w : List Alphabet) (depth : Nat) : Bool :=
  match depth with
  | 0 => true
  | depth + 1 =>
    [a, b, c, d].all (fun x =>
      let w_next := w ++ [x]
      if isSquareFreeSuffixBoundary w_next 1 then
        let gx := g x
        if check_prefixes_g_optimized g_w gx then
          dfs_check_optimized w_next (g_w ++ gx) depth
        else false
      else true)
termination_by depth
decreasing_by all_goals (simp_wf; try omega)

/-
Computational verification for length 4 (optimized).
-/
lemma check_keranen : dfs_check_optimized [] [] 4 = true := by native_decide


#print axioms check_keranen
